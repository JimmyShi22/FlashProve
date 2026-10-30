-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/Kc/Kit.lean: the rules by which the statement "this flat function is that routine"
(`Sim`, OnBytes/K/Kc/Laws.lean) passes through the text of a routine, and the statement itself for
each call on the channel and each small step on the state.

 - How a run of a routine of a sub-proof is taken apart: `sub_pure`, `sub_bind`, `sub_lift`,
   `sub_must`, `sub_get`, `sub_change`, `sub_ask`, `sub_take`.
 - The rules: `Sim.pure`, `Sim.bind`, `Sim.lift`, `Sim.must`, `Sim.need`, `Sim.change`, `Sim.take`,
   `Sim.ask`, `Sim.foldlM`.
 - The calls on the channel, from the laws of OnBytes/Iop/GroundLaws.lean and OnBytes/Slice/:
   `simB_recvE`, `simB_trRead`, `closeAs_inv` (with `Closed`), `simB_trAnswer`,
   `simB_trAnswerNotZero`, `simB_trPoint`, `simB_trBatchOpen`, `simB_trBatch`, `simB_trEmpty`.

Not claimed. Nothing on the dry run. Nothing on soundness. The program does not import this file.
-/
import OnBytes.K.Kc.Laws
import OnBytes.Slice.BlkCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc

open OnBytes.Model (Fork SubM)

variable {α β γ : Type}

/-! ## A run of a routine, taken apart -/

/-- A run that returns, as an equation. -/
theorem runs_iff (m : SubM α) (F G : Fork) (c c' : Ctx) (a : α) :
    (m F).Yields c (a, G) c' ↔ m F c = .ok ((a, G), c') :=
  Blk.yields_iff _ _ _ _

/-- A routine that only returns a value. -/
theorem sub_pure (a x : α) (F G : Fork) (c c' : Ctx) :
    ((pure a : SubM α) F).Yields c (x, G) c' ↔ x = a ∧ G = F ∧ c' = c := by
  show (pure (a, F) : Blk (α × Fork)).Yields c (x, G) c' ↔ _
  rw [Blk.yields_pure]
  constructor
  · rintro ⟨h1, h2⟩
    cases h1
    exact ⟨rfl, rfl, h2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- Two routines, one after the other. -/
theorem sub_bind (m : SubM α) (k : α → SubM β) (F G : Fork) (c c' : Ctx) (b : β) :
    ((m >>= k) F).Yields c (b, G) c' ↔
      ∃ (a : α) (F1 : Fork) (c1 : Ctx),
        (m F).Yields c (a, F1) c1 ∧ (k a F1).Yields c1 (b, G) c' := by
  show ((m F >>= fun p => k p.1 p.2 : Blk (β × Fork))).Yields c (b, G) c' ↔ _
  rw [Blk.yields_bind]
  constructor
  · rintro ⟨⟨a, F1⟩, c1, h1, h2⟩
    exact ⟨a, F1, c1, h1, h2⟩
  · rintro ⟨a, F1, c1, h1, h2⟩
    exact ⟨(a, F1), c1, h1, h2⟩

/-- A block as a routine: it runs, and the state stays as it was. -/
theorem sub_lift (x : Blk α) (F G : Fork) (c c' : Ctx) (a : α) :
    ((StateT.lift x : SubM α) F).Yields c (a, G) c' ↔ x.Yields c a c' ∧ G = F := by
  show ((x >>= fun y => pure (y, F) : Blk (α × Fork))).Yields c (a, G) c' ↔ _
  rw [Blk.yields_bind]
  constructor
  · rintro ⟨y, c1, h1, h2⟩
    obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).mp h2
    cases e1
    subst e2
    exact ⟨h1, rfl⟩
  · rintro ⟨h1, rfl⟩
    exact ⟨a, c', h1, (Blk.yields_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩

theorem sub_get (x : Option α) (F G : Fork) (c c' : Ctx) (a : α) :
    (SubM.get x F).Yields c (a, G) c' ↔ x = some a ∧ G = F ∧ c' = c := by
  unfold SubM.get
  rw [sub_lift, Blk.yields_get]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h3, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3⟩, h2⟩

theorem sub_must (b : Bool) (F G : Fork) (c c' : Ctx) :
    (SubM.must b F).Yields c ((), G) c' ↔ b = true ∧ G = F ∧ c' = c := by
  unfold SubM.must
  rw [sub_lift, Blk.yields_must]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h3, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3⟩, h2⟩

theorem sub_change (f : Fork → Option Fork) (F G : Fork) (c c' : Ctx) :
    (SubM.change f F).Yields c ((), G) c' ↔ f F = some G ∧ c' = c := by
  rw [runs_iff]
  simp only [SubM.change]
  cases f F with
  | none => simp [liftOption_none]
  | some H => simp [liftOption_some, eq_comm]

theorem sub_ask (f : Fork → Option α) (F G : Fork) (c c' : Ctx) (a : α) :
    (SubM.ask f F).Yields c (a, G) c' ↔ f F = some a ∧ G = F ∧ c' = c := by
  rw [runs_iff]
  simp only [SubM.ask]
  cases f F with
  | none => simp [liftOption_none]
  | some y => simp [liftOption_some, eq_comm, and_assoc]

theorem sub_take (f : Fork → Option (α × Fork)) (F G : Fork) (c c' : Ctx) (a : α) :
    (SubM.take f F).Yields c (a, G) c' ↔ f F = some (a, G) ∧ c' = c := by
  rw [runs_iff]
  simp only [SubM.take]
  cases f F with
  | none => simp [liftOption_none]
  | some y => simp [liftOption_some, eq_comm]

/-! ## The rules -/

theorem Sim.pure (a : α) : Sim (Pure.pure a : SubM α) (Pure.pure a : Fl α) := by
  intro F G C D x hd h
  obtain ⟨rfl, rfl, rfl⟩ := (sub_pure _ _ _ _ _ _).mp h
  exact ⟨rfl, Left.refl hd⟩

theorem Sim.bind {X : SubM α} {K : α → SubM β} {f : Fl α} {g : α → Fl β} (h1 : Sim X f)
    (h2 : ∀ a, Sim (K a) (g a)) : Sim (X >>= K) (f >>= g) := by
  intro F G C D b hd h
  obtain ⟨a, F1, C1, r1, r2⟩ := (sub_bind _ _ _ _ _ _ _).mp h
  obtain ⟨e1, d1⟩ := h1 F F1 C C1 a hd r1
  obtain ⟨e2, d2⟩ := h2 a F1 G C1 D b d1.dry r2
  refine ⟨?_, d1.trans d2⟩
  show Fl.andThen f g F (tape C) = _
  unfold Fl.andThen
  rw [e1]
  exact e2

theorem Sim.lift {x : Blk α} {g : Tape → Option (α × Tape)} (h : SimB x g) :
    Sim (StateT.lift x : SubM α) (Fl.onTape g) := by
  intro F G C D a hd r
  obtain ⟨r1, rfl⟩ := (sub_lift _ _ _ _ _ _).mp r
  obtain ⟨e, d⟩ := h C D a hd r1
  refine ⟨?_, d⟩
  unfold Fl.onTape
  rw [e]
  rfl

theorem Sim.must (b : Bool) : Sim (SubM.must b) (Fl.must b) := by
  intro F G C D u hd r
  cases u
  obtain ⟨rfl, rfl, rfl⟩ := (sub_must _ _ _ _ _).mp r
  exact ⟨rfl, Left.refl hd⟩

theorem Sim.need (x : Option α) : Sim (SubM.get x) (Fl.need x) := by
  intro F G C D a hd r
  obtain ⟨rfl, rfl, rfl⟩ := (sub_get _ _ _ _ _ _).mp r
  exact ⟨rfl, Left.refl hd⟩

theorem Sim.change (f : Fork → Option Fork) : Sim (SubM.change f) (Fl.change f) := by
  intro F G C D u hd r
  cases u
  obtain ⟨e, rfl⟩ := (sub_change _ _ _ _ _).mp r
  refine ⟨?_, Left.refl hd⟩
  unfold Fl.change
  rw [e]
  rfl

theorem Sim.take (f : Fork → Option (α × Fork)) : Sim (SubM.take f) (Fl.take f) := by
  intro F G C D a hd r
  obtain ⟨e, rfl⟩ := (sub_take _ _ _ _ _ _).mp r
  refine ⟨?_, Left.refl hd⟩
  unfold Fl.take
  rw [e]
  rfl

theorem Sim.ask (f : Fork → Option α) : Sim (SubM.ask f) (Fl.ask f) := by
  intro F G C D a hd r
  obtain ⟨e, rfl, rfl⟩ := (sub_ask _ _ _ _ _ _).mp r
  refine ⟨?_, Left.refl hd⟩
  unfold Fl.ask
  rw [e]
  rfl

theorem Sim.foldlM (X : β → γ → SubM β) (f : β → γ → Fl β) (h : ∀ b c, Sim (X b c) (f b c)) :
    ∀ (l : List γ) (b : β), Sim (l.foldlM X b) (l.foldlM f b)
  | [], b => by
    rw [List.foldlM_nil, List.foldlM_nil]
    exact Sim.pure b
  | c :: l, b => by
    rw [List.foldlM_cons, List.foldlM_cons]
    exact Sim.bind (h b c) fun b' => Sim.foldlM X f h l b'

/-! ## The calls on the channel -/

/-- A public condition under a name that passes was true, and it changes nothing. -/
theorem mustAs_inv (n : String) (b : Bool) (c c' : Ctx) (u : Unit)
    (h : (Model.mustAs n b).Yields c u c') : b = true ∧ c' = c := by
  rw [Blk.yields_iff] at h
  cases b with
  | false => cases h
  | true =>
    cases h
    exact ⟨rfl, rfl⟩

/-- The first of the rounds with its entry, if there is one, and the others with theirs. -/
theorem paired_cons (r : Fmt.RoundView) (rest : List Fmt.RoundView) (es : List Fmt.Entry) :
    paired (r :: rest) es = flatOf r es.head? :: paired rest es.tail := by
  cases es <;> rfl

/-- Taking an element off the first round, on the tape. -/
theorem recv_flatOf (r : Fmt.RoundView) (e : Option Fmt.Entry) (x : E) (vs : List Fmt.ItemValue) (T : Tape)
    (h : r.vals = .e x.triple :: vs) :
    recv (flatOf r e :: T) = some (x, flatOf { r with vals := vs } e :: T) := by
  unfold flatOf
  rw [h]
  rfl

theorem simB_recvE : SimB Blk.recvE recv := by
  intro C D x hd h
  obtain ⟨r, rest, vs, e1, e2, e3, e4⟩ := Blk.recvE_inv x C D hd h
  refine ⟨?_, ⟨by rw [e4.dry]; exact hd, e4.st, e4.book, e4.failed, e4.opened, e4.roots,
    e4.firstTree, e4.samples, ?_⟩⟩
  · unfold tape
    rw [e1, e3, e4.entries, paired_cons, paired_cons]
    exact recv_flatOf r _ x vs _ e2
  · rw [e1, e3, e4.entries, e4.last, e4.asked]
    exact .item e2 (.refl _ _ _ _)

theorem simB_trReadLoop : ∀ (n : Nat) (a : Array E), SimB (Model.trReadLoop n a) (recvLoop n a)
  | 0, a => by
    intro C D v hd h
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).mp h
    exact ⟨rfl, Left.refl hd⟩
  | n + 1, a => by
    intro C D v hd h
    obtain ⟨x, C1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).mp h
    obtain ⟨e1, d1⟩ := simB_recvE C C1 x hd h1
    obtain ⟨e2, d2⟩ := simB_trReadLoop n (a.push x) C1 D v d1.dry h2
    refine ⟨?_, d1.trans d2⟩
    show (match recv (tape C) with
      | some (x, u) => recvLoop n (a.push x) u
      | none => none) = _
    rw [e1]
    exact e2

theorem simB_trRead (n : Nat) : SimB (Model.trRead n) (recvN n) :=
  simB_trReadLoop n _

section CloseMore

open Blk

/-- In a run on a view, two things more of a round that was closed than `Blk.close_inv` says: the
round closed before owed no question on its rows, and the rows of this one are not yet asked. The
proof is that theorem's, with another end. -/
theorem close_more (name : String) (kind : Fmt.Kind) (nz : Nat) (d : Fmt.Drawn) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (close name kind nz).Yields c d c') :
    c.ch.settled = true ∧ c'.ch.askedRows = false := by
  rw [yields_iff] at h
  unfold close at h
  cases he : c.ch.entries with
  | nil => simp [he] at h
  | cons e es =>
    simp only [he] at h
    by_cases hg : (e.name != name || e.drawNZ != nz || !c.ch.settled) = true
    · simp [hg] at h
    · have hd' : ¬ (c.ch.dry = true) := by simp [hd]
      simp only [hg, Bool.false_eq_true, if_false, hd'] at h
      have hg' : c.ch.settled = true := by
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or] at hg
        cases hs : c.ch.settled with
        | true => rfl
        | false => exact absurd hs hg.2
      have hx : ∃ r t, c.ch.pending = r :: t ∧
          (if (r.vals.isEmpty && r.drawn.elems.length == e.drawE &&
              r.drawn.poss.length == e.poss && r.drawn.trits.length == e.trits) = true then
            Except.ok (r.drawn, { c with ch := { c.ch with
              dry := false, entries := es, last := some e, askedRows := false, cur := none,
              left := t } })
          else Except.error ({ name := shapeName } : Failure)) = .ok (d, c') := by
        cases hc : c.ch.cur with
        | some r =>
          simp only [hc] at h
          exact ⟨r, c.ch.left, by simp [Chan.pending, hc], h⟩
        | none =>
          simp only [hc] at h
          cases hl : c.ch.left with
          | nil => simp [hl] at h
          | cons r t =>
            simp only [hl] at h
            exact ⟨r, t, by simp [Chan.pending, hc, hl], h⟩
      obtain ⟨r, t, _, hh⟩ := hx
      by_cases hk : (r.vals.isEmpty && r.drawn.elems.length == e.drawE &&
            r.drawn.poss.length == e.poss && r.drawn.trits.length == e.trits) = true
      · simp only [hk, if_true, Except.ok.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        exact ⟨hg', rfl⟩
      · simp [hk] at hh

end CloseMore

/-- What `closeAs_inv` says of a round that `Model.closeAs` has closed. -/
structure Closed (name : String) (elems nz : Nat) (d : Fmt.Drawn) (C D : Ctx) (e : Fmt.Entry)
    (es : List Fmt.Entry) (r : Fmt.RoundView) (rest : List Fmt.RoundView) : Prop where
  entries : C.ch.entries = e :: es
  named : e.name = name
  notZero : e.drawNZ = nz
  pending : C.ch.pending = r :: rest
  taken : r.vals = []
  drawn : d = r.drawn
  count : d.elems.length = elems
  pending' : D.ch.pending = rest
  entries' : D.ch.entries = es
  last : D.ch.last = some e
  asked : D.ch.askedRows = false
  settled : C.ch.settled = true
  left : Left C D

/-- In a run on a view: a round that `Model.closeAs` has closed was the first round not yet closed,
all its items had been taken, the plan's next entry had the name and the number of elements drawn
other than 0 that the call names, and it drew the number of elements that the call names. -/
theorem closeAs_inv (name : String) (kind : Fmt.Kind) (elems nz entries : Nat) (d : Fmt.Drawn)
    (C D : Ctx) (hd : C.ch.dry = false)
    (h : (Model.closeAs name kind elems nz entries).Yields C d D) :
    ∃ e es r rest, Closed name elems nz d C D e es r rest := by
  unfold Model.closeAs at h
  obtain ⟨_, C1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).mp h
  obtain ⟨_, rfl⟩ := (Blk.yields_must _ _ _).mp h1
  obtain ⟨d', C2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).mp k1
  obtain ⟨e', C3, h3, k3⟩ := (Blk.yields_bind _ _ _ _ _).mp k2
  obtain ⟨l1, rfl⟩ := (Slice.yields_lastEntry _ _ _).mp h3
  obtain ⟨_, C4, h4, k4⟩ := (Blk.yields_bind _ _ _ _ _).mp k3
  obtain ⟨m1, rfl⟩ := (Blk.yields_must _ _ _).mp h4
  obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).mp k4
  obtain ⟨e, es, r, rest, q1, q2, q3, p1, p2, p3, p4, q4, q5, p5, q6, p6, q7, q8, q9, p7, q10,
    q11, q12, q13⟩ := Blk.close_inv name kind nz _ _ _ hd h2
  rw [p6] at l1
  have ee : e = e' := Option.some.inj l1
  simp only [Bool.and_eq_true, beq_iff_eq] at m1
  have hl : d.elems.length = elems := by
    rw [p4, ee]
    exact m1.1.1
  obtain ⟨hs, ha⟩ := close_more name kind nz _ _ _ hd h2
  refine ⟨e, es, r, rest, q1, q2, q3, p1, p2, p3, hl, p5, q6, p6, ha, hs,
    ⟨p7, q7, q8, q9, q10, q11, q12, q13, ?_⟩⟩
  rw [p1, q1, p5, q6, p6, ha]
  exact .close p2 (by rw [← p3]; exact p4) (by rw [← p3]; exact q4) (by rw [← p3]; exact q5)
    (.refl _ _ _ _)

/-- The one element that `Model.oneOf` returns is all that the round drew. -/
theorem oneOf_inv (d : Fmt.Drawn) (x : E) (c c' : Ctx) (h : (Model.oneOf d).Yields c x c') :
    d.elems = [x.triple] ∧ c' = c := by
  unfold Model.oneOf at h
  cases hel : d.elems with
  | nil =>
    rw [hel] at h
    cases h
  | cons a l =>
    cases l with
    | nil =>
      rw [hel] at h
      obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).mp h
      exact ⟨by rw [E.triple_ofTriple], rfl⟩
    | cons a' l' =>
      rw [hel] at h
      cases h

/-- The closed round as plain data. -/
theorem Closed.flat {name : String} {elems nz : Nat} {d : Fmt.Drawn} {C D : Ctx} {e : Fmt.Entry}
    {es : List Fmt.Entry} {r : Fmt.RoundView} {rest : List Fmt.RoundView}
    (c : Closed name elems nz d C D e es r rest) :
    tape C = ⟨some name, nz, e.rows, [], d.elems.map E.ofTriple⟩ :: tape D := by
  unfold tape
  rw [c.pending, c.entries, c.pending', c.entries']
  show flatOf r (some e) :: paired rest es = _
  unfold flatOf
  rw [c.taken, ← c.drawn]
  show FlatRound.mk (some e.name) e.drawNZ e.rows [] _ :: _ = _
  rw [c.named, c.notZero]

/-- A round that was closed for one element, on the tape. -/
theorem closeOne_of {name : String} {elems nz : Nat} {d : Fmt.Drawn} {C D : Ctx} {e : Fmt.Entry}
    {es : List Fmt.Entry} {r : Fmt.RoundView} {rest : List Fmt.RoundView}
    (c : Closed name elems nz d C D e es r rest) (x : E) (p4 : d.elems = [x.triple]) :
    closeOne name nz (tape C) = some (x, tape D) := by
  rw [c.flat, p4]
  show (if (name == name && nz == nz) = true then some (x, tape D) else none) = _
  rw [beq_self_eq_true, beq_self_eq_true]
  rfl

/-- A round that was closed for n elements, on the tape. -/
theorem closeN_of {name : String} {n nz : Nat} {d : Fmt.Drawn} {C D : Ctx} {e : Fmt.Entry}
    {es : List Fmt.Entry} {r : Fmt.RoundView} {rest : List Fmt.RoundView}
    (c : Closed name n nz d C D e es r rest) :
    closeN name nz n (tape C) = some (d.elems.map E.ofTriple, tape D) := by
  rw [c.flat]
  show (if (name == name && nz == nz && (d.elems.map E.ofTriple).length == n) = true then
    some (d.elems.map E.ofTriple, tape D) else none) = _
  rw [List.length_map, c.count, beq_self_eq_true, beq_self_eq_true, beq_self_eq_true]
  rfl

theorem simB_trAnswer (r : Model.RoundName) : SimB (Model.trAnswer r) (closeOne r.name 0) := by
  intro C D x hd h
  unfold Model.trAnswer at h
  obtain ⟨_, C1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).mp h
  obtain ⟨_, rfl⟩ := mustAs_inv _ _ _ _ _ h1
  obtain ⟨d, C2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).mp k1
  obtain ⟨q, rfl⟩ := oneOf_inv _ _ _ _ k2
  obtain ⟨e, es, r0, rest, c⟩ := closeAs_inv _ _ _ _ _ _ _ _ hd h2
  exact ⟨closeOne_of c x q, c.left⟩

theorem simB_trAnswerNotZero (r : Model.RoundName) :
    SimB (Model.trAnswerNotZero r) (closeOne r.name 1) := by
  intro C D x hd h
  unfold Model.trAnswerNotZero at h
  obtain ⟨_, C1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).mp h
  obtain ⟨_, rfl⟩ := mustAs_inv _ _ _ _ _ h1
  obtain ⟨d, C2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).mp k1
  obtain ⟨q, rfl⟩ := oneOf_inv _ _ _ _ k2
  obtain ⟨e, es, r0, rest, c⟩ := closeAs_inv _ _ _ _ _ _ _ _ hd h2
  exact ⟨closeOne_of c x q, c.left⟩

theorem simB_trPoint (r : Model.RoundName) (n : Nat) :
    SimB (Model.trPoint r n) (Fl.pointOn r.name n) := by
  intro C D v hd h
  unfold Model.trPoint at h
  obtain ⟨_, C1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).mp h
  obtain ⟨_, rfl⟩ := mustAs_inv _ _ _ _ _ h1
  obtain ⟨d, C2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).mp k1
  obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).mp k2
  obtain ⟨e, es, r0, rest, c⟩ := closeAs_inv _ _ _ _ _ _ _ _ hd h2
  refine ⟨?_, c.left⟩
  unfold Fl.pointOn
  rw [closeN_of c]
  rfl

theorem simB_trEmpty (r : Model.RoundName) : SimB (Model.trEmpty r) (Fl.emptyOn r.name) := by
  intro C D u hd h
  unfold Model.trEmpty at h
  obtain ⟨d, C2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).mp h
  obtain ⟨_, rfl⟩ := (Blk.yields_pure _ _ _ _).mp k2
  obtain ⟨e, es, r0, rest, c⟩ := closeAs_inv _ _ _ _ _ _ _ _ hd h2
  refine ⟨?_, c.left⟩
  unfold Fl.emptyOn
  rw [closeN_of c]
  rfl

/-- The round of a batching element, as it was closed. -/
theorem trBatchOpen_closed (x : E) (C D : Ctx) (hd : C.ch.dry = false)
    (h : Model.trBatchOpen.Yields C x D) :
    ∃ d e es r rest, Closed Model.RoundName.batSigma.name 1 0 d C D e es r rest := by
  unfold Model.trBatchOpen at h
  obtain ⟨d, C2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).mp h
  obtain ⟨_, rfl⟩ := oneOf_inv _ _ _ _ k2
  obtain ⟨e, es, r0, rest, c⟩ := closeAs_inv _ _ _ _ _ _ _ _ hd h2
  exact ⟨d, e, es, r0, rest, c⟩

/-- The round of a batching element, before its rows are asked. -/
theorem simB_trBatchOpen :
    SimB Model.trBatchOpen (closeOne Model.RoundName.batSigma.name 0) := by
  intro C D x hd h
  unfold Model.trBatchOpen at h
  obtain ⟨d, C2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).mp h
  obtain ⟨q, rfl⟩ := oneOf_inv _ _ _ _ k2
  obtain ⟨e, es, r0, rest, c⟩ := closeAs_inv _ _ _ _ _ _ _ _ hd h2
  exact ⟨closeOne_of c x q, c.left⟩

theorem simB_trBatch (rows : Nat) : SimB (Model.trBatch rows) (Fl.batchOn rows) := by
  intro C D v hd h
  unfold Model.trBatch at h
  obtain ⟨_, C1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).mp h
  obtain ⟨hr, rfl⟩ := mustAs_inv _ _ _ _ _ h1
  obtain ⟨x, C2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).mp k1
  unfold Model.trBatchOpen at h2
  obtain ⟨d, C3, h3, k3⟩ := (Blk.yields_bind _ _ _ _ _).mp h2
  obtain ⟨q, rfl⟩ := oneOf_inv _ _ _ _ k3
  obtain ⟨e, es, r0, rest, c⟩ := closeAs_inv _ _ _ _ _ _ _ _ hd h3
  obtain ⟨_, C4, h4, k4⟩ := (Blk.yields_bind _ _ _ _ _).mp k2
  obtain ⟨e', l1, l2, rfl⟩ := Slice.requireRows_inv rows _ _ c.left.dry h4
  obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).mp k4
  have ee : e = e' := Option.some.inj (c.last.symm.trans l1)
  have l := c.left
  refine ⟨?_, ⟨l.dry, l.st, l.book, l.failed, l.opened, l.roots, l.firstTree, l.samples,
    l.eats.trans (.asked (.refl _ _ _ _))⟩⟩
  unfold Fl.batchOn
  rw [if_pos hr, c.flat, q]
  show Option.map _ (if (Model.RoundName.batSigma.name == Model.RoundName.batSigma.name && 0 == 0 &&
    e.rows == rows) = true then some (x, tape _) else none) = _
  rw [ee, l2, beq_self_eq_true, beq_self_eq_true, beq_self_eq_true]
  rfl

end OnBytes.K.Kc
