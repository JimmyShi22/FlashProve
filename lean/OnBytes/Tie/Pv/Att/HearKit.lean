-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/HearKit.lean: what the calls between attention's sumchecks have heard and done
where they succeed: the round that batches rows, the round that draws a point, hidden values that
ride in a message, and a sumcheck of products with its row.

Main names:
  batch_ok: SubM.batch n (OnBytes/Model/Hide.lean): n is not 0; the state is untouched; the open
    message's round is closed under the name BAT-sigma for one element x; the number of rows is
    compared; the powers of x are returned.
  point_ok: SubM.point .zero n: the state is untouched; the open message's round is closed under the
    name ZERO; the elements drawn are returned.
  claimsIn_said: SubM.claimsIn n from a state whose arrays on slots have their length: n elements
    are received and nothing is closed; they stand under the next n slots; the state behind has its
    arrays' length.
  Parts.ride: further scalars that were received before a sumcheck's first message are its riders
    (Parts, OnBytes/Tie/Pv/Psc/Run/PscSeam.lean).
  sc3_sized: behind the messages and the row of a sumcheck of products the arrays on slots have
    their length.

Limits: one direction: from a call's success. On a view and in the dry run alike. How many elements
the round ZERO has drawn is the plan's entry's number, which closeAs compares; that the returned
array has that size is not said here.
-/
import OnBytes.Tie.Pv.Att.Sc3Top
import OnBytes.Tie.Pv.Att.ScdTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Attention
open OnBytes.Psc (Weight hearMany hearOne)

/-- The round that batches rows. -/
theorem batch_ok (n : Nat) (F G : Fork) (c c' : Ctx) (w : Array E)
    (h : SubM.batch n F c = .ok ((w, G), c')) :
    n ≠ 0 ∧ G = F ∧ ∃ (x : E) (c1 : Ctx),
      (Blk.closeOne RoundName.batSigma.name .elems 0).Yields c x c1 ∧
      (Blk.requireRows n).Yields c1 () c' ∧ w = powers x n := by
  unfold SubM.batch at h
  obtain ⟨y, e⟩ := (liftY_ok _ _ _ _ _ _).1 h
  unfold trBatch at y
  obtain ⟨_, c0, h0, k0⟩ := (Blk.yields_bind _ _ _ _ _).1 y
  obtain ⟨m1, m2⟩ := (mustAs_ok _ _ _ _ _).1 ((Blk.yields_iff _ _ _ _).1 h0)
  obtain ⟨x, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 k0
  obtain ⟨_, c2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
  obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 k2
  unfold trBatchOpen at h1
  obtain ⟨d, c3, h3, k3⟩ := (Blk.yields_bind _ _ _ _ _).1 h1
  rw [m2] at h3
  refine ⟨by simpa using m1, e, x, c1,
    oneOf_closeOne _ _ _ d x _ c3 _ (closeAs_close _ _ _ _ _ _ _ _ h3) k3, ?_, e1⟩
  rw [e2]
  exact h2

/-- The round that draws a point. -/
theorem point_ok (n : Nat) (F G : Fork) (c c' : Ctx) (pts : Array E)
    (h : SubM.point .zero n F c = .ok ((pts, G), c')) :
    G = F ∧ ∃ d : Fmt.Drawn, (Blk.close RoundName.zero.name .elems 0).Yields c d c' ∧
      pts = (d.elems.map E.ofTriple).toArray := by
  unfold SubM.point at h
  obtain ⟨y, e⟩ := (liftY_ok _ _ _ _ _ _).1 h
  unfold trPoint at y
  obtain ⟨_, c0, h0, k0⟩ := (Blk.yields_bind _ _ _ _ _).1 y
  obtain ⟨_, m2⟩ := (mustAs_ok _ _ _ _ _).1 ((Blk.yields_iff _ _ _ _).1 h0)
  obtain ⟨d, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 k0
  obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 k1
  rw [m2] at h1
  refine ⟨e, d, ?_, e1⟩
  rw [e2]
  exact closeAs_close _ _ _ _ _ _ _ _ h1

/-- Hidden values that ride in a message. -/
theorem claimsIn_said (n : Nat) (F G : Fork) (c c' : Ctx) (j : Nat)
    (h : SubM.claimsIn n F c = .ok ((j, G), c')) (hz : Sized F) :
    ∃ v : List E, (Blk.recvEs n).Yields c v c' ∧ v.length = n ∧ j = F.next ∧
      Filled (taken F n) G F.next v oneE ∧ Sized G := by
  obtain ⟨v, a1, a2, a3, a4⟩ := claimsIn_ok n F G c c' j h
  have f := hideRun_ok _ _ _ _ _ a4 (sized_taken F n hz)
  exact ⟨v.toList, a1, by simpa using a2, a3, f, f.sized⟩

/-- Scalars received before a sumcheck's first message are its riders. -/
theorem Parts.ride {c c1 c' : Ctx} {riders : List E} {mu eps : E} {ws : List Weight}
    {rs : List (List E × E)} {dY : Nat} {sentY : List E} {beta : E} {v : List E}
    (h0 : (Blk.recvEs riders.length).Yields c riders c1)
    (a : Parts c1 c1 c' [] mu eps ws rs dY sentY beta v) :
    Parts c c1 c' riders mu eps ws rs dY sentY beta v := by
  obtain ⟨c2, c3, c4, c5, _, h1, h2, h3, h4, h5⟩ := a
  exact ⟨c2, c3, c4, c5, h0, h1, h2, h3, h4, h5⟩

theorem sc3_sized (nv nb : Nat) (C : Aff) (W : Array E) (o1 o : Attention.Sc3) (F F2 G : Fork)
    (c c2 c' : Ctx) (h1 : sc3In nv nb C F c = .ok ((o1, F2), c2))
    (h2 : sc3Row o1 W F2 c2 = .ok ((o, G), c')) (hz : Sized F) : Sized G := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, a⟩ := sc3In_seam _ _ _ o1 F F2 c c2 h1 hz
  obtain ⟨_, _, _, _, _, _, _, b⟩ := sc3Row_ok o1 o W F2 G c2 c' h2 a.sized
  exact b.sized

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.batch_ok
#print axioms OnBytes.Tie.Pv.Att.point_ok
#print axioms OnBytes.Tie.Pv.Att.claimsIn_said
#print axioms OnBytes.Tie.Pv.Att.Parts.ride
#print axioms OnBytes.Tie.Pv.Att.sc3_sized
