-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Psc/PscView.lean: what the calls of the channel's routines take off a view: a round
at a time.

Definitions, and theorems with their proofs. A run on a view (not a dry run) holds in its channel
(`Chan`, OnBytes/Iop/Ground.lean) the rounds that are not yet begun (`left`) and the round whose
message is being received (`cur`). Here: if the calls that make up one round
(OnBytes/Tie/Pv/Psc/PscRun.lean: `Ev`, `Evs`) lead from a context without an open message to
another, they have taken exactly one round off `left`, the elements received are the field elements
among that round's items, the elements drawn are that round's, and again no message is open.

OnBytes/Iop/GroundLaws.lean has laws on the same single calls (`item_inv`, `recvE_inv`, `close_inv`,
over `Chan.pending`, with what a call leaves as it was). The laws on single calls here also say
which of `cur` and `left` holds what: after a closing no message is open. The rounds' laws are put
together from that.

Main names:
  `sentOf rv`, `drawnOf rv`: the field elements among a round's items; the elements that it draws.
  `Clean c`: a run on a view, no message open.
  `pending c`: the open round with the items not yet taken, if there is one, then the rounds not
    begun (`Chan.pending`).
  `recvE_view`, `trRead_view`, `close_view`, `closeAs_view`: single calls.
  `Round c rv c'`: c and c' are clean and rv is the one round between them.
  `round_sum`, `round_read`, `round_readNZ`, `round_values`, `round_ans`, `round_point`: the six
    kinds of round of a lookup.
  `Took c rvs c'`: the same for a list of rounds; `Took.append`.

Limits: nothing on a dry run, on the plan's entries or on a run that fails. Of the context after a
round only the channel's `dry`, `cur` and `left` are spoken of, and of a round only its items and
the elements that it draws. `round_sum` begins where no message is open, so the sum is alone in its
message.


-/
import OnBytes.Iop.GroundLaws
import OnBytes.Tie.Pv.Psc.PscRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.PscRun
open OnBytes OnBytes.Model

/-- The field element that an item of a message holds, if it is one. -/
def eOf : Fmt.ItemValue → Option E
  | .e x => some (E.ofTriple x)
  | _ => none

/-- The field elements among a round's items. -/
def sentOf (r : Fmt.RoundView) : List E := r.vals.filterMap eOf

/-- The elements that a round draws. -/
def drawnOf (r : Fmt.RoundView) : List E := r.drawn.elems.map E.ofTriple

/-- A run on a view, no message open. -/
def Clean (c : Ctx) : Prop := c.ch.dry = false ∧ c.ch.cur = none

/-- What of the view is not yet taken. -/
def pending (c : Ctx) : List Fmt.RoundView := c.ch.pending

section Blk
variable {α β : Type}

/-- A run of «x, then f» in `Blk`. -/
theorem bindB_ok (x : Blk α) (f : α → Blk β) (c : Ctx) (r : β × Ctx) :
    (x >>= f) c = .ok r ↔ ∃ a c1, x c = .ok (a, c1) ∧ f a c1 = .ok r := by
  show (x c >>= fun p => f p.1 p.2) = .ok r ↔ _
  cases h : x c with
  | error e =>
    show (Except.error e : Except Failure _) = .ok r ↔ _
    simp
  | ok y =>
    obtain ⟨a, c1⟩ := y
    show f a c1 = .ok r ↔ _
    simp only [Except.ok.injEq, Prod.mk.injEq]
    constructor
    · intro h'
      exact ⟨a, c1, ⟨rfl, rfl⟩, h'⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h'⟩
      exact h'

/-- A block that only returns a value leaves the context. -/
theorem pureB_ok (a : α) (c : Ctx) (r : α × Ctx) : (pure a : Blk α) c = .ok r ↔ r = (a, c) := by
  show (Except.ok (a, c) : Except Failure _) = .ok r ↔ _
  simp [eq_comm]

/-- A public condition in `Blk`. -/
theorem mustB_ok (b : Bool) (name : String) (c : Ctx) (r : Unit × Ctx) :
    Blk.must b name c = .ok r ↔ b = true ∧ r = ((), c) := by
  cases b <;> simp [Blk.must, eq_comm]

/-- A public condition under a name. -/
theorem mustAs_ok (name : String) (b : Bool) (c : Ctx) (r : Unit × Ctx) :
    mustAs name b c = .ok r ↔ b = true ∧ r = ((), c) := by
  cases b with
  | false => simp [mustAs, refuse, Blk.fail]
  | true =>
    simp only [mustAs, if_true, true_and]
    exact pureB_ok () c r

end Blk

/-- One item is taken. -/
theorem item_view (i : Fmt.Item) (dflt g : Fmt.ItemValue) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : Blk.item i dflt c = .ok (g, c')) :
    ∃ r t gs, pending c = r :: t ∧ r.vals = g :: gs ∧ c'.ch.dry = false ∧
      c'.ch.cur = some { r with vals := gs } ∧ c'.ch.left = t := by
  unfold Blk.item at h
  rw [hd] at h
  simp only [Bool.false_eq_true, if_false] at h
  unfold pending Chan.pending
  cases hc : c.ch.cur with
  | some r =>
    rw [hc] at h
    simp only [] at h
    cases hv : r.vals with
    | nil => rw [hv] at h; simp at h
    | cons g0 gs =>
      rw [hv] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨r, _, gs, rfl, hv, hd, rfl, rfl⟩
  | none =>
    rw [hc] at h
    simp only [] at h
    cases hl : c.ch.left with
    | nil => rw [hl] at h; simp at h
    | cons r t =>
      rw [hl] at h
      simp only [] at h
      cases hv : r.vals with
      | nil => rw [hv] at h; simp at h
      | cons g0 gs =>
        rw [hv] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨r, t, gs, rfl, hv, hd, rfl, rfl⟩

/-- One element is received. -/
theorem recvE_view (x : E) (c c' : Ctx) (hd : c.ch.dry = false) (h : Blk.recvE c = .ok (x, c')) :
    ∃ r t gs y, pending c = r :: t ∧ r.vals = .e y :: gs ∧ x = E.ofTriple y ∧ c'.ch.dry = false ∧
      c'.ch.cur = some { r with vals := gs } ∧ c'.ch.left = t := by
  unfold Blk.recvE at h
  rw [bindB_ok] at h
  obtain ⟨g, c1, h1, h⟩ := h
  obtain ⟨r, t, gs, hp, hv, hd', hc', hl'⟩ := item_view _ _ _ _ _ hd h1
  cases g with
  | e y =>
    simp only [] at h
    rw [pureB_ok] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨r, t, gs, y, hp, hv, rfl, hd', hc', hl'⟩
  | f _ => simp [Blk.fail] at h
  | word _ => simp [Blk.fail] at h
  | root _ => simp [Blk.fail] at h
  | answer _ => simp [Blk.fail] at h

/-- n elements are received. -/
theorem trReadLoop_view : ∀ (n : Nat) (a v : Array E) (c c' : Ctx), c.ch.dry = false →
    trReadLoop n a c = .ok (v, c') →
    (n = 0 ∧ v = a ∧ c' = c) ∨
      ∃ (r : Fmt.RoundView) (t : List Fmt.RoundView) (ys : List (UInt64 × UInt64 × UInt64)) (gs : List Fmt.ItemValue),
        ys.length = n ∧ pending c = r :: t ∧ r.vals = ys.map Fmt.ItemValue.e ++ gs ∧
        v.toList = a.toList ++ ys.map E.ofTriple ∧ c'.ch.dry = false ∧
        c'.ch.cur = some { r with vals := gs } ∧ c'.ch.left = t
  | 0, a, v, c, c', _, h => by
    unfold trReadLoop at h
    rw [pureB_ok] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact Or.inl ⟨rfl, rfl, rfl⟩
  | n + 1, a, v, c, c', hd, h => by
    unfold trReadLoop at h
    rw [bindB_ok] at h
    obtain ⟨x, c1, h1, h⟩ := h
    obtain ⟨r, t, gs, y, hp, hv, rfl, hd1, hc1, hl1⟩ := recvE_view _ _ _ hd h1
    refine Or.inr ?_
    rcases trReadLoop_view n _ _ _ _ hd1 h with
      ⟨rfl, rfl, rfl⟩ | ⟨r', t', ys, gs', hn, hp', hv', hl, hd', hc', hl'⟩
    · exact ⟨r, t, [y], gs, rfl, hp, hv, by simp, hd1, hc1, hl1⟩
    · have e : ({ r with vals := gs } : Fmt.RoundView) :: t = r' :: t' := by
        rw [← hp']
        unfold pending Chan.pending
        rw [hc1, hl1]
      obtain ⟨rfl, rfl⟩ := List.cons.inj e
      refine ⟨r, t, y :: ys, gs', by simp [hn], hp, ?_, ?_, hd', hc', hl'⟩
      · rw [hv]
        have : gs = ys.map Fmt.ItemValue.e ++ gs' := hv'
        rw [this]
        rfl
      · rw [hl]
        simp

/-- n elements are received, from the empty array. -/
theorem trRead_view (n : Nat) (v : Array E) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : trRead n c = .ok (v, c')) :
    (n = 0 ∧ v.toList = [] ∧ c' = c) ∨
      ∃ (r : Fmt.RoundView) (t : List Fmt.RoundView) (ys : List (UInt64 × UInt64 × UInt64)) (gs : List Fmt.ItemValue),
        ys.length = n ∧ pending c = r :: t ∧ r.vals = ys.map Fmt.ItemValue.e ++ gs ∧
        v.toList = ys.map E.ofTriple ∧ c'.ch.dry = false ∧
        c'.ch.cur = some { r with vals := gs } ∧ c'.ch.left = t := by
  unfold trRead at h
  rcases trReadLoop_view n _ _ _ _ hd h with ⟨rfl, rfl, rfl⟩ | ⟨r, t, ys, gs, hn, hp, hv, hl, h3⟩
  · exact Or.inl ⟨rfl, by simp, rfl⟩
  · exact Or.inr ⟨r, t, ys, gs, hn, hp, hv, by simpa using hl, h3⟩

/-- A round is closed. -/
theorem close_view (name : String) (kind : Fmt.Kind) (nz : Nat) (d : Fmt.Drawn) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : Blk.close name kind nz c = .ok (d, c')) :
    ∃ r t e, pending c = r :: t ∧ r.vals = [] ∧ d = r.drawn ∧ c'.ch.last = some e ∧
      r.drawn.elems.length = e.drawE ∧ Clean c' ∧ c'.ch.left = t := by
  unfold Blk.close at h
  cases he : c.ch.entries with
  | nil => rw [he] at h; simp at h
  | cons e es =>
    rw [he] at h
    simp only [hd, Bool.false_eq_true, if_false] at h
    split at h
    · simp at h
    · cases hc : c.ch.cur with
      | some r =>
        rw [hc] at h
        simp only [] at h
        split at h
        · rename_i hq
          simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hq
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨r, c.ch.left, e, by unfold pending Chan.pending; rw [hc], hq.1.1.1, rfl, rfl,
            hq.1.1.2, ⟨rfl, rfl⟩, rfl⟩
        · simp at h
      | none =>
        rw [hc] at h
        cases hl : c.ch.left with
        | nil => rw [hl] at h; simp at h
        | cons r t =>
          rw [hl] at h
          simp only [] at h
          split at h
          · rename_i hq
            simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hq
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨r, t, e, by unfold pending Chan.pending; rw [hc, hl], hq.1.1.1, rfl, rfl,
              hq.1.1.2, ⟨rfl, rfl⟩, rfl⟩
          · simp at h

/-- A round is closed against the plan: it also draws as many elements as the call says. -/
theorem closeAs_view (name : String) (kind : Fmt.Kind) (elems notZero entries : Nat) (d : Fmt.Drawn)
    (c c' : Ctx) (hd : c.ch.dry = false)
    (h : closeAs name kind elems notZero entries c = .ok (d, c')) :
    ∃ r t, pending c = r :: t ∧ r.vals = [] ∧ d = r.drawn ∧ r.drawn.elems.length = elems ∧
      Clean c' ∧ c'.ch.left = t := by
  unfold closeAs at h
  rw [bindB_ok] at h
  obtain ⟨_, c1, h1, h⟩ := h
  rw [mustB_ok] at h1
  obtain ⟨-, e1⟩ := h1
  obtain ⟨-, rfl⟩ := Prod.mk.inj e1
  rw [bindB_ok] at h
  obtain ⟨d0, c2, h2, h⟩ := h
  obtain ⟨r, t, e, hp, hv, rfl, hlast, hlen, hcl, hl⟩ := close_view _ _ _ _ _ _ hd h2
  rw [bindB_ok] at h
  obtain ⟨e', c3, h3, h⟩ := h
  unfold Blk.lastEntry at h3
  rw [hlast] at h3
  simp only [Except.ok.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  rw [bindB_ok] at h
  obtain ⟨_, c4, h4, h⟩ := h
  rw [mustB_ok] at h4
  obtain ⟨hm, e4⟩ := h4
  obtain ⟨-, rfl⟩ := Prod.mk.inj e4
  rw [pureB_ok] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  simp only [Bool.and_eq_true, beq_iff_eq] at hm
  exact ⟨r, t, hp, hv, rfl, hlen.trans hm.1.1, hcl, hl⟩

/-- c and c' are clean, and rv is the one round of the view between them. -/
def Round (c : Ctx) (rv : Fmt.RoundView) (c' : Ctx) : Prop :=
  Clean c ∧ Clean c' ∧ c.ch.left = rv :: c'.ch.left

/-- The field elements among items that are all field elements. -/
theorem sentOf_es (ys : List (UInt64 × UInt64 × UInt64)) (d : Fmt.Drawn) :
    sentOf ⟨ys.map Fmt.ItemValue.e, d⟩ = ys.map E.ofTriple := by
  unfold sentOf
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    show E.ofTriple y :: (ys.map Fmt.ItemValue.e).filterMap eOf = _
    rw [show (ys.map Fmt.ItemValue.e).filterMap eOf = ys.map E.ofTriple from ih]
    rfl

/-- A message of n elements is received from a clean context, and its round is then closed. -/
theorem read_close (n : Nat) (v : Array E) (c c1 c' : Ctx) (d : Fmt.Drawn) (k : Nat) (hc : Clean c)
    (h1 : trRead n c = .ok (v, c1))
    (h2 : ∃ r t, pending c1 = r :: t ∧ r.vals = [] ∧ d = r.drawn ∧ r.drawn.elems.length = k ∧
      Clean c' ∧ c'.ch.left = t) :
    ∃ rv, Round c rv c' ∧ sentOf rv = v.toList ∧ rv.drawn = d ∧ d.elems.length = k := by
  obtain ⟨r', t', hp', hv', rfl, hk, hcl, hl⟩ := h2
  have hpc : pending c = c.ch.left := by
    unfold pending Chan.pending
    rw [hc.2]
  rcases trRead_view n v c c1 hc.1 h1 with
    ⟨-, hv, rfl⟩ | ⟨r, t, ys, gs, -, hp, hvals, hv, hd1, hc1, hl1⟩
  · rw [hpc] at hp'
    refine ⟨r', ⟨hc, hcl, by rw [hp', hl]⟩, ?_, rfl, hk⟩
    unfold sentOf
    rw [hv', hv]
    rfl
  · have e : ({ r with vals := gs } : Fmt.RoundView) :: t = r' :: t' := by
      rw [← hp']
      unfold pending Chan.pending
      rw [hc1, hl1]
    obtain ⟨rfl, rfl⟩ := List.cons.inj e
    have hgs : gs = [] := hv'
    subst hgs
    rw [hpc] at hp
    refine ⟨r, ⟨hc, hcl, by rw [hp, hl]⟩, ?_, rfl, hk⟩
    rw [hv]
    obtain ⟨vals, dr⟩ := r
    have : vals = ys.map Fmt.ItemValue.e := by simpa using hvals
    subst this
    exact sentOf_es ys dr

/-- The one element that a round has drawn. -/
theorem oneOf_ok (d : Fmt.Drawn) (x : E) (c c' : Ctx) (h : oneOf d c = .ok (x, c')) :
    d.elems.map E.ofTriple = [x] ∧ c' = c := by
  unfold oneOf at h
  cases he : d.elems with
  | nil =>
    rw [he] at h
    simp [Blk.fail] at h
  | cons y l =>
    cases l with
    | nil =>
      rw [he] at h
      simp only [] at h
      rw [pureB_ok] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨rfl, rfl⟩
    | cons _ _ =>
      rw [he] at h
      simp [Blk.fail] at h

/-- A round is closed and one element drawn. -/
theorem trAnswer_view (r : RoundName) (x : E) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : trAnswer r c = .ok (x, c')) :
    ∃ d, d.elems.map E.ofTriple = [x] ∧ ∃ rv t, pending c = rv :: t ∧ rv.vals = [] ∧ d = rv.drawn ∧
      rv.drawn.elems.length = 1 ∧ Clean c' ∧ c'.ch.left = t := by
  unfold trAnswer at h
  rw [bindB_ok] at h
  obtain ⟨_, c1, h1, h⟩ := h
  unfold noBatching at h1
  rw [mustAs_ok] at h1
  obtain ⟨-, e1⟩ := h1
  obtain ⟨-, rfl⟩ := Prod.mk.inj e1
  rw [bindB_ok] at h
  obtain ⟨d, c2, h2, h⟩ := h
  obtain ⟨hx, rfl⟩ := oneOf_ok _ _ _ _ h
  exact ⟨d, hx, closeAs_view _ _ _ _ _ _ _ _ hd h2⟩

/-- A round is closed and one element drawn by the rule that never gives 0. -/
theorem trAnswerNotZero_view (r : RoundName) (x : E) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : trAnswerNotZero r c = .ok (x, c')) :
    ∃ d, d.elems.map E.ofTriple = [x] ∧ ∃ rv t, pending c = rv :: t ∧ rv.vals = [] ∧ d = rv.drawn ∧
      rv.drawn.elems.length = 1 ∧ Clean c' ∧ c'.ch.left = t := by
  unfold trAnswerNotZero at h
  rw [bindB_ok] at h
  obtain ⟨_, c1, h1, h⟩ := h
  unfold noBatching at h1
  rw [mustAs_ok] at h1
  obtain ⟨-, e1⟩ := h1
  obtain ⟨-, rfl⟩ := Prod.mk.inj e1
  rw [bindB_ok] at h
  obtain ⟨d, c2, h2, h⟩ := h
  obtain ⟨hx, rfl⟩ := oneOf_ok _ _ _ _ h
  exact ⟨d, hx, closeAs_view _ _ _ _ _ _ _ _ hd h2⟩

/-- A round is closed in which nothing is drawn. -/
theorem trEmpty_view (r : RoundName) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : trEmpty r c = .ok ((), c')) :
    ∃ d rv t, pending c = rv :: t ∧ rv.vals = [] ∧ d = rv.drawn ∧
      rv.drawn.elems.length = 0 ∧ Clean c' ∧ c'.ch.left = t := by
  unfold trEmpty at h
  rw [bindB_ok] at h
  obtain ⟨d, c2, h2, h⟩ := h
  rw [pureB_ok] at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj h
  exact ⟨d, closeAs_view _ _ _ _ _ _ _ _ hd h2⟩

/-- A round is closed and n elements are drawn. -/
theorem trPoint_view (r : RoundName) (n : Nat) (v : Array E) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : trPoint r n c = .ok (v, c')) :
    ∃ d, d.elems.map E.ofTriple = v.toList ∧ ∃ rv t, pending c = rv :: t ∧ rv.vals = [] ∧
      d = rv.drawn ∧ rv.drawn.elems.length = n ∧ Clean c' ∧ c'.ch.left = t := by
  unfold trPoint at h
  rw [bindB_ok] at h
  obtain ⟨_, c1, h1, h⟩ := h
  unfold noBatching at h1
  rw [mustAs_ok] at h1
  obtain ⟨-, e1⟩ := h1
  obtain ⟨-, rfl⟩ := Prod.mk.inj e1
  rw [bindB_ok] at h
  obtain ⟨d, c2, h2, h⟩ := h
  rw [pureB_ok] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  exact ⟨d, by simp, closeAs_view _ _ _ _ _ _ _ _ hd h2⟩

/-- The context after a reading on a view is on a view. -/
theorem trRead_onView (n : Nat) (v : Array E) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : trRead n c = .ok (v, c')) : c'.ch.dry = false := by
  rcases trRead_view n v c c' hd h with ⟨-, -, rfl⟩ | ⟨_, _, _, _, -, -, -, -, h', -⟩
  · exact hd
  · exact h'

/-- A round in which n elements are received and one is drawn. -/
theorem round_read (n : Nat) (v : Array E) (r : RoundName) (x : E) (c c' : Ctx) (hc : Clean c)
    (h : Evs [.read n v, .ans r x] c c') :
    ∃ rv, Round c rv c' ∧ sentOf rv = v.toList ∧ drawnOf rv = [x] := by
  obtain ⟨c1, h1, c2, h2, rfl⟩ := h
  obtain ⟨d, hx, hcl⟩ := trAnswer_view r x c1 _ (trRead_onView _ _ _ _ hc.1 h1) h2
  obtain ⟨rv, hr, hs, hd, -⟩ := read_close n v c c1 _ d 1 hc h1 hcl
  exact ⟨rv, hr, hs, by unfold drawnOf; rw [hd, hx]⟩

/-- The same with the draw that never gives 0. -/
theorem round_readNZ (n : Nat) (v : Array E) (r : RoundName) (x : E) (c c' : Ctx) (hc : Clean c)
    (h : Evs [.read n v, .ansNZ r x] c c') :
    ∃ rv, Round c rv c' ∧ sentOf rv = v.toList ∧ drawnOf rv = [x] := by
  obtain ⟨c1, h1, c2, h2, rfl⟩ := h
  obtain ⟨d, hx, hcl⟩ := trAnswerNotZero_view r x c1 _ (trRead_onView _ _ _ _ hc.1 h1) h2
  obtain ⟨rv, hr, hs, hd, -⟩ := read_close n v c c1 _ d 1 hc h1 hcl
  exact ⟨rv, hr, hs, by unfold drawnOf; rw [hd, hx]⟩

/-- A round in which n elements are received and nothing is drawn. -/
theorem round_values (n : Nat) (v : Array E) (r : RoundName) (c c' : Ctx) (hc : Clean c)
    (h : Evs [.read n v, .empty r] c c') :
    ∃ rv, Round c rv c' ∧ sentOf rv = v.toList ∧ drawnOf rv = [] := by
  obtain ⟨c1, h1, c2, h2, rfl⟩ := h
  obtain ⟨d, hcl⟩ := trEmpty_view r c1 _ (trRead_onView _ _ _ _ hc.1 h1) h2
  obtain ⟨rv, hr, hs, hd, hk⟩ := read_close n v c c1 _ d 0 hc h1 hcl
  refine ⟨rv, hr, hs, ?_⟩
  unfold drawnOf
  rw [hd, List.length_eq_zero_iff.1 hk]
  rfl

/-- The round in which the sum of a hiding polynomial is received and one element is drawn. -/
theorem round_sum (mu : E) (r : RoundName) (x : E) (c c' : Ctx) (hc : Clean c)
    (h : Evs [.sum mu, .ans r x] c c') :
    ∃ rv, Round c rv c' ∧ sentOf rv = [mu] ∧ drawnOf rv = [x] := by
  obtain ⟨c1, h1, c2, h2, rfl⟩ := h
  obtain ⟨r0, t, gs, y, hp, hv, rfl, hd1, hc1, hl1⟩ := recvE_view _ _ _ hc.1 h1
  obtain ⟨d, hx, r', t', hp', hv', rfl, -, hcl, hl⟩ := trAnswer_view r x c1 _ hd1 h2
  have e : ({ r0 with vals := gs } : Fmt.RoundView) :: t = r' :: t' := by
    rw [← hp']
    unfold pending Chan.pending
    rw [hc1, hl1]
  obtain ⟨rfl, rfl⟩ := List.cons.inj e
  have hgs : gs = [] := hv'
  subst hgs
  have hpc : pending c = c.ch.left := by
    unfold pending Chan.pending
    rw [hc.2]
  rw [hpc] at hp
  refine ⟨r0, ⟨hc, hcl, by rw [hp, hl]⟩, ?_, hx⟩
  unfold sentOf
  rw [hv]
  rfl

/-- A round in which nothing is received and one element is drawn. -/
theorem round_ans (r : RoundName) (x : E) (c c' : Ctx) (hc : Clean c) (h : Evs [.ans r x] c c') :
    ∃ rv, Round c rv c' ∧ sentOf rv = [] ∧ drawnOf rv = [x] := by
  obtain ⟨c1, h1, rfl⟩ := h
  obtain ⟨d, hx, r', t', hp', hv', rfl, -, hcl, hl⟩ := trAnswer_view r x c _ hc.1 h1
  have hpc : pending c = c.ch.left := by
    unfold pending Chan.pending
    rw [hc.2]
  rw [hpc] at hp'
  refine ⟨r', ⟨hc, hcl, by rw [hp', hl]⟩, ?_, hx⟩
  unfold sentOf
  rw [hv']
  rfl

/-- A round in which nothing is received and n elements are drawn. -/
theorem round_point (r : RoundName) (n : Nat) (v : Array E) (c c' : Ctx) (hc : Clean c)
    (h : Evs [.point r n v] c c') :
    ∃ rv, Round c rv c' ∧ sentOf rv = [] ∧ drawnOf rv = v.toList ∧ v.size = n := by
  obtain ⟨c1, h1, rfl⟩ := h
  obtain ⟨d, hx, r', t', hp', hv', rfl, hk, hcl, hl⟩ := trPoint_view r n v c _ hc.1 h1
  have hpc : pending c = c.ch.left := by
    unfold pending Chan.pending
    rw [hc.2]
  rw [hpc] at hp'
  refine ⟨r', ⟨hc, hcl, by rw [hp', hl]⟩, ?_, hx, ?_⟩
  · unfold sentOf
    rw [hv']
    rfl
  · have := congrArg List.length hx
    simpa [hk] using this.symm

/-- c and c' are clean, and the rounds rvs of the view lie between them. -/
def Took (c : Ctx) (rvs : List Fmt.RoundView) (c' : Ctx) : Prop :=
  Clean c ∧ Clean c' ∧ c.ch.left = rvs ++ c'.ch.left

/-- No round. -/
theorem Took.nil {c : Ctx} (h : Clean c) : Took c [] c := ⟨h, h, rfl⟩

/-- One round as a list of rounds. -/
theorem Round.took {c c' : Ctx} {rv : Fmt.RoundView} (h : Round c rv c') : Took c [rv] c' := h

/-- Rounds after rounds. -/
theorem Took.append {c c1 c2 : Ctx} {l m : List Fmt.RoundView} (h : Took c l c1) (h' : Took c1 m c2) :
    Took c (l ++ m) c2 :=
  ⟨h.1, h'.2.1, by rw [h.2.2, h'.2.2, List.append_assoc]⟩

end OnBytes.PscRun

#print axioms OnBytes.PscRun.round_sum
#print axioms OnBytes.PscRun.round_read
#print axioms OnBytes.PscRun.round_readNZ
#print axioms OnBytes.PscRun.round_values
#print axioms OnBytes.PscRun.round_ans
#print axioms OnBytes.PscRun.round_point
