-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/ViewRounds.lean: on a view, what the block's listeners have heard are rounds
of the view, taken off it one by one, and the lists heard are what these rounds hold; also where
scalars were received before the round's own listener was called.

The laws on single calls are the library's (Blk.recvE_inv, OnBytes/Iop/GroundLaws.lean, over
Chan.pending) and those of OnBytes/Tie/Pv/Psc/PscView.lean (close_view, Clean, Took), which follows
the model's calls round by round from contexts without an open message. Here the same is said of the
block's own listeners (Blk.recvEs, Blk.close, Blk.closeOne; hearOne, hearMany, OnBytes/Iop/Psc.lean;
Parts, OnBytes/Tie/Pv/Psc/Run/PscSeam.lean), and a message may be open where a listener begins: so
the further scalars of a sumcheck's first message are covered.

Main names:
  Ate A l A': the elements l were taken, as items of the kind e, off the first of the rounds A, and
    A' is left. Ate.trans.
  recvEs_view: elements received on a view are the next items of the first round that is not yet
    closed.
  Holds r l: the round r holds the elements l and no other item. holds_sent: then sentOf r = l.
  round_view: elements received and then a round closed: one round r: c.ch.pending = r ::
    c'.ch.pending, Holds r l, what was drawn is r.drawn, and no message is open behind it.
  closeOne_close: what Blk.closeOne has closed and drawn.
  RoundH, IsRound, RoundsAre: a round as it was heard (what was sent; what was drawn, where that is
    said); a round, and a list of rounds, of a view hold what was heard.
  hearOne_view, hearMany_view: the listeners of a masked sumcheck's rounds.
  parts_view: a whole masked sumcheck with riders: the riders and mu, with eps; each variable's
    scalars, with its challenge; the scalars of the further variable, with beta; the end values.
  parts_took: the same from a context without an open message, in the form Took c rvs c'.

Limits: one direction: from a listener's success. On a view alone. Of the round of the end values
nothing is said on what was drawn. If a message is open at c, the first round of c.ch.pending is
what is left of that round, not the view's whole round. Nothing is said on how a view is made from a
file or from a transcript.
-/
import OnBytes.Tie.Pv.Psc.Run.PscSeam
import OnBytes.Tie.Pv.Psc.PscView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Road
open OnBytes OnBytes.Model
open OnBytes.Psc (Weight hearMany hearOne)
open OnBytes.PscRun (Clean Took sentOf drawnOf)

/-- The elements l were taken, as items of the kind e, off the first of the rounds A; A' is left. -/
def Ate (A : List Fmt.RoundView) (l : List E) (A' : List Fmt.RoundView) : Prop :=
  (l = [] ∧ A' = A) ∨ ∃ (r : Fmt.RoundView) (t : List Fmt.RoundView) (gs : List Fmt.ItemValue), A = r :: t ∧
    r.vals = l.map (fun x => Fmt.ItemValue.e x.triple) ++ gs ∧ A' = { r with vals := gs } :: t

theorem Ate.nil (A : List Fmt.RoundView) : Ate A [] A := Or.inl ⟨rfl, rfl⟩

theorem Ate.trans {A B C : List Fmt.RoundView} {l m : List E} (h1 : Ate A l B) (h2 : Ate B m C) :
    Ate A (l ++ m) C := by
  rcases h1 with ⟨rfl, rfl⟩ | ⟨r, t, gs, a1, a2, a3⟩
  · exact h2
  · rcases h2 with ⟨rfl, rfl⟩ | ⟨r', t', gs', b1, b2, b3⟩
    · rw [List.append_nil]
      exact Or.inr ⟨r, t, gs, a1, a2, a3⟩
    · rw [a3] at b1
      obtain ⟨e1, e2⟩ := List.cons.inj b1
      subst e1 e2
      refine Or.inr ⟨r, t, gs', a1, ?_, b3⟩
      rw [a2, List.map_append, List.append_assoc]
      exact congrArg _ b2

theorem recvEsInto_view : ∀ (n : Nat) (acc a : Array E) (c c' : Ctx), c.ch.dry = false →
    (Blk.recvEsInto n acc).Yields c a c' →
    ∃ l : List E, l.length = n ∧ a.toList = acc.toList ++ l ∧
      Ate c.ch.pending l c'.ch.pending ∧ c'.ch.dry = false
  | 0, acc, a, c, c', hd, h => by
    obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 h
    rw [e1, e2]
    exact ⟨[], rfl, by simp, Ate.nil _, hd⟩
  | n + 1, acc, a, c, c', hd, h => by
    simp only [Blk.recvEsInto] at h
    obtain ⟨x, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨r, t, gs, a1, a2, a3, a4⟩ := Blk.recvE_inv x c c1 hd h1
    obtain ⟨l, b1, b2, b3, b4⟩ := recvEsInto_view n _ a c1 c' (a4.dry.trans hd) h2
    refine ⟨x :: l, by rw [List.length_cons, b1], ?_,
      Ate.trans (l := [x]) (Or.inr ⟨r, t, gs, a1, a2, a3⟩) b3, b4⟩
    rw [b2]
    simp

/-- Elements received on a view are the next items of the first round that is not yet closed. -/
theorem recvEs_view {n : Nat} {l : List E} {c c' : Ctx} (hd : c.ch.dry = false)
    (h : (Blk.recvEs n).Yields c l c') :
    l.length = n ∧ Ate c.ch.pending l c'.ch.pending ∧ c'.ch.dry = false := by
  unfold Blk.recvEs at h
  obtain ⟨a, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 h2
  obtain ⟨l', b1, b2, b3, b4⟩ := recvEsInto_view n #[] a c c1 hd h1
  have e : l = l' := by rw [e1, b2]; simp
  rw [e2, e]
  exact ⟨b1, b3, b4⟩

theorem pending_clean {c : Ctx} (h : Clean c) : c.ch.pending = c.ch.left := by
  simp [Chan.pending, h.2]

/-- The round r of a view holds the elements l and no other item. -/
def Holds (r : Fmt.RoundView) (l : List E) : Prop := r.vals = l.map fun x => Fmt.ItemValue.e x.triple

/-- Then the field elements among the round's items are l. -/
theorem holds_sent {r : Fmt.RoundView} {l : List E} (h : Holds r l) : sentOf r = l := by
  obtain ⟨vals, d⟩ := r
  have h' : vals = (l.map (·.triple)).map Fmt.ItemValue.e := by
    rw [List.map_map]
    exact h
  subst h'
  rw [OnBytes.PscRun.sentOf_es, List.map_map]
  exact List.map_id' l

/-- Elements received and then a round closed: one round of the view. -/
theorem round_view {n : Nat} {l : List E} {name : String} {kind : Fmt.Kind} {nz : Nat}
    {d : Fmt.Drawn} {c c1 c' : Ctx} (hd : c.ch.dry = false) (h1 : (Blk.recvEs n).Yields c l c1)
    (h2 : (Blk.close name kind nz).Yields c1 d c') :
    ∃ r : Fmt.RoundView, c.ch.pending = r :: c'.ch.pending ∧ Holds r l ∧ d = r.drawn ∧ Clean c' := by
  obtain ⟨_, a3, a4⟩ := recvEs_view hd h1
  obtain ⟨r1, t, _, b1, b2, b3, _, _, b5, b6⟩ :=
    OnBytes.PscRun.close_view name kind nz d c1 c' a4 ((Blk.yields_iff _ _ _ _).1 h2)
  have b1' : c1.ch.pending = r1 :: t := b1
  have b4 : c'.ch.pending = t := by rw [pending_clean b5, b6]
  rcases a3 with ⟨e1, e2⟩ | ⟨r, t', gs, e1, e2, e3⟩
  · rw [e2] at b1'
    exact ⟨r1, by rw [b1', b4], by rw [Holds, b2, e1]; rfl, b3, b5⟩
  · rw [e3] at b1'
    obtain ⟨f1, f2⟩ := List.cons.inj b1'
    subst f1 f2
    have hg : gs = [] := b2
    exact ⟨r, by rw [e1, b4], by rw [Holds, e2, hg, List.append_nil], b3, b5⟩

/-- What closeOne has closed and drawn. -/
theorem closeOne_close {name : String} {kind : Fmt.Kind} {nz : Nat} {x : E} {c c' : Ctx}
    (h : (Blk.closeOne name kind nz).Yields c x c') :
    ∃ (d : Fmt.Drawn) (y : UInt64 × UInt64 × UInt64), (Blk.close name kind nz).Yields c d c' ∧
      d.elems = [y] ∧ x = E.ofTriple y := by
  unfold Blk.closeOne at h
  obtain ⟨d, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  cases he : d.elems with
  | nil => rw [he] at h2; rw [Blk.yields_iff] at h2; cases h2
  | cons y l =>
    cases l with
    | nil =>
      rw [he] at h2
      obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 h2
      rw [e2]
      exact ⟨d, y, h1, he, e1⟩
    | cons _ _ => rw [he] at h2; rw [Blk.yields_iff] at h2; cases h2

/-- One round as it was heard: what was sent; what was drawn, where that is said. -/
abbrev RoundH : Type := List E × Option (List E)

/-- The round of a view holds what was heard. -/
def IsRound (r : Fmt.RoundView) (h : RoundH) : Prop := Holds r h.1 ∧ ∀ l, h.2 = some l → l = drawnOf r

/-- The rounds of a view hold what was heard, one by one. -/
def RoundsAre : List RoundH → List Fmt.RoundView → Prop
  | [], [] => True
  | h :: hs, r :: rs => IsRound r h ∧ RoundsAre hs rs
  | _, _ => False

theorem RoundsAre.append : ∀ {a b : List RoundH} {x y : List Fmt.RoundView}, RoundsAre a x →
    RoundsAre b y → RoundsAre (a ++ b) (x ++ y)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, h1, h2 => ⟨h1.1, RoundsAre.append h1.2 h2⟩
  | [], _, _ :: _, _, h1, _ => h1.elim
  | _ :: _, _, [], _, h1, _ => h1.elim

/-- A round in which elements are sent and one element is drawn. -/
theorem hearOne_view {name : String} {kind : Fmt.Kind} {n nz : Nat} {q : List E} {g : E}
    {c c' : Ctx} (hd : c.ch.dry = false) (h : (hearOne name kind n nz).Yields c (q, g) c') :
    ∃ r : Fmt.RoundView, c.ch.pending = r :: c'.ch.pending ∧ IsRound r (q, some [g]) ∧ Clean c' := by
  unfold hearOne at h
  obtain ⟨q', c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨g', c2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
  obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 k2
  obtain ⟨f1, f2⟩ := Prod.mk.inj e1
  subst f1 f2 e2
  obtain ⟨d, y, a1, a2, a3⟩ := closeOne_close h2
  obtain ⟨r, b1, b2, b3, b4⟩ := round_view hd h1 a1
  refine ⟨r, b1, ⟨b2, fun l hl => ?_⟩, b4⟩
  rw [← Option.some.inj hl, drawnOf, ← b3, a2, a3]
  rfl

theorem hearMany_view : ∀ (ns : List Nat) (rs : List (List E × E)) (c c' : Ctx), Clean c →
    (hearMany ns).Yields c rs c' →
    ∃ rv : List Fmt.RoundView, c.ch.pending = rv ++ c'.ch.pending ∧
      RoundsAre (rs.map fun x => (x.1, some [x.2])) rv ∧ Clean c'
  | [], rs, c, c', hc, h => by
    obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 h
    rw [e1, e2]
    exact ⟨[], rfl, trivial, hc⟩
  | n :: ns, rs, c, c', hc, h => by
    simp only [hearMany] at h
    obtain ⟨a, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨l, c2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
    obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 k2
    obtain ⟨r, a1, a2, a3⟩ := hearOne_view (q := a.1) (g := a.2) hc.1 h1
    obtain ⟨rv, b1, b2, b3⟩ := hearMany_view ns l c1 c2 a3 h2
    rw [e1, e2]
    exact ⟨r :: rv, by rw [a1, b1]; rfl, ⟨a2, b2⟩, b3⟩

/-- The rounds of a masked sumcheck with riders, as they were heard. -/
def partsRounds (riders : List E) (mu eps : E) (rs : List (List E × E)) (sentY : List E) (beta : E)
    (v : List E) : List RoundH :=
  (riders ++ [mu], some [eps]) :: (rs.map fun x => (x.1, some [x.2])) ++
    [(sentY, some [beta]), (v, none)]

/-- A sumcheck's rounds on a view. A message may be open at c. -/
theorem parts_view {c c1 c' : Ctx} {riders : List E} {mu eps : E} {ws : List Weight}
    {rs : List (List E × E)} {dY : Nat} {sentY : List E} {beta : E} {v : List E}
    (hd : c.ch.dry = false) (a : Parts c c1 c' riders mu eps ws rs dY sentY beta v) :
    ∃ rv : List Fmt.RoundView, c.ch.pending = rv ++ c'.ch.pending ∧
      RoundsAre (partsRounds riders mu eps rs sentY beta v) rv ∧ Clean c' := by
  obtain ⟨c2, c3, c4, c5, h1, h2, h3, h4, h5⟩ := a.whole
  obtain ⟨r1, a1, a2, a3⟩ := hearOne_view hd h1
  obtain ⟨rv, b1, b2, b3⟩ := hearMany_view _ rs c2 c3 a3 h2
  obtain ⟨rY, d1, d2, d3⟩ := hearOne_view b3.1 h3
  unfold Blk.closeEmpty at h5
  obtain ⟨d, c6, k1, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 h5
  obtain ⟨_, e2⟩ := (Blk.yields_pure _ _ _ _).1 k2
  obtain ⟨rV, f1, f2, _, f4⟩ := round_view d3.1 h4 k1
  rw [e2]
  refine ⟨r1 :: (rv ++ [rY, rV]), ?_, ⟨a2, RoundsAre.append b2 ⟨d2,
    ⟨f2, fun _ hl => nomatch hl⟩, trivial⟩⟩, f4⟩
  rw [a1, b1, d1, f1]
  simp

/-- The same from a context without an open message. -/
theorem parts_took {c c1 c' : Ctx} {riders : List E} {mu eps : E} {ws : List Weight}
    {rs : List (List E × E)} {dY : Nat} {sentY : List E} {beta : E} {v : List E}
    (hc : Clean c) (a : Parts c c1 c' riders mu eps ws rs dY sentY beta v) :
    ∃ rv : List Fmt.RoundView, Took c rv c' ∧
      RoundsAre (partsRounds riders mu eps rs sentY beta v) rv := by
  obtain ⟨rv, a1, a2, a3⟩ := parts_view hc.1 a
  rw [pending_clean hc, pending_clean a3] at a1
  exact ⟨rv, ⟨hc, a3, a1⟩, a2⟩

end OnBytes.Model.Road

#print axioms OnBytes.Model.Road.recvEs_view
#print axioms OnBytes.Model.Road.holds_sent
#print axioms OnBytes.Model.Road.round_view
#print axioms OnBytes.Model.Road.hearOne_view
#print axioms OnBytes.Model.Road.hearMany_view
#print axioms OnBytes.Model.Road.parts_view
#print axioms OnBytes.Model.Road.parts_took
