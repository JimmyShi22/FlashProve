-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscRun.lean: what a successful run of pscBeginAt, pscRound, roundIn, pscEnds
and tscLoop has heard, how the running claim stepped, and which slots were taken.

The routines are those of OnBytes/Model/Psc.lean and OnBytes/Model/Tsc.lean. What they heard is said
in the words of the block's own listener (OnBytes/Iop/Psc.lean: hearOne, hearMany, hear).

Main names:
  `taken F n`: the state F with n more slots taken.
  `pscBeginAt_ok`: one element mu is received and the round PSC epsilon is closed; the record that
    is left; one slot is taken.
  `pscRound_ok`, `roundIn_ok`: one round: the elements received, the draw, the tests on the weight,
    the next claim, the slots.
  `Stepped p p' ws rs`: p' is p after the rounds rs under the weights ws. `Stepped.nil`,
    `Stepped.cons`.
  `tscLoop_ok`: the token sumcheck's rounds, one under the equality weight of each coordinate.
  `pscEnds_ok`: the round PSC Y under Weight.atZero, then n end values in the round PSC values. The
    values are put under the next n slots with the factor beta.
  `hear_of`: the parts of a sumcheck with end values make the block's hear succeed.
Limits: one direction only, from a success of the model's routine. That mu is the last element of
its round's message is not in pscBeginAt_ok. No statement has a hypothesis on whether the channel is
a view or the dry run. Nothing is said on hiding.
-/
import OnBytes.Tie.Pv.Psc.Run.PscKit

namespace OnBytes.Model.Road
open OnBytes.Psc (Weight hearOne hearMany hear claimAfter polyAt)

/-- F with n more slots taken. -/
def taken (F : Fork) (n : Nat) : Fork := { F with next := F.next + n }

theorem taken_taken (F : Fork) (a b : Nat) : taken (taken F a) b = taken F (a + b) := by
  simp only [taken, Nat.add_assoc]

theorem taken_zero (F : Fork) : taken F 0 = F := rfl

theorem recvE_recvEs (x : E) (c c' : Ctx) (h : Blk.recvE.Yields c x c') :
    (Blk.recvEs 1).Yields c [x] c' := by
  unfold Blk.recvEs
  refine (Blk.yields_bind _ _ _ _ _).2 ⟨#[x], c', ?_, (Blk.yields_pure _ _ _ _).2 ⟨rfl, rfl⟩⟩
  simp only [Blk.recvEsInto]
  exact (Blk.yields_bind _ _ _ _ _).2 ⟨x, c', h, (Blk.yields_pure _ _ _ _).2 ⟨rfl, rfl⟩⟩

/-- The beginning: from the context in which it is called, one item (mu) is received and the round
"PSC epsilon" is closed. That mu is the last item of that round's message is not in this statement.
On a view it follows from close, which refuses while items are left. -/
theorem pscBeginAt_ok (τ : E) (F G : Fork) (c c' : Ctx) (p : Psc)
    (h : pscBeginAt τ F c = .ok ((p, G), c')) :
    ∃ mu, (hearOne "PSC epsilon" .join 1 0).Yields c ([mu], p.eps) c' ∧
      p = { target := τ, first := F.next, eps := p.eps, claim := addE mu (mulE p.eps τ) } ∧
      G = taken F 1 := by
  unfold pscBeginAt at h
  obtain ⟨first, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨e1, e2, e3⟩ := (takeSlots_ok _ _ _ _ _ _).1 h1
  obtain ⟨mu, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨y2, e4⟩ := (liftY_ok _ _ _ _ _ _).1 h2
  obtain ⟨eps, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨y3, e5⟩ := (liftY_ok _ _ _ _ _ _).1 h3
  obtain ⟨e6, e7, e8⟩ := (pure_ok _ _ _ _ _ _).1 k3
  subst e1 e2 e3 e4 e5 e6 e7 e8
  exact ⟨mu, hearOne_of _ _ _ _ _ _ _ _ _ (recvE_recvEs _ _ _ y2) (trAnswer_closeOne _ _ _ _ y3),
    rfl, rfl⟩

/-- One round, whatever closes it. -/
theorem pscRound_ok (p p' : Psc) (w : Weight) (draw : Blk E) (F G : Fork) (c c' : Ctx) (r : E)
    (h : pscRound p w draw F c = .ok (((r, p'), G), c')) :
    ∃ sent c1, (Blk.recvEs (w.d - 1)).Yields c sent c1 ∧ draw.Yields c1 r c' ∧
      w.fits = true ∧ weightHeld w = true ∧ sent.length + 1 = w.d ∧
      p' = { p with claim := polyAt (w.complete sent p.claim) r, vars := p.vars.push w,
                    r := p.r.push r } ∧
      G = taken F (w.d - 1) := by
  unfold pscRound at h
  obtain ⟨_, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨b1, e1, e2⟩ := (must_ok _ _ _ _ _ _).1 h1
  obtain ⟨sent, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨y2, e3⟩ := (liftY_ok _ _ _ _ _ _).1 h2
  obtain ⟨_, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨b3, e4, e5⟩ := (must_ok _ _ _ _ _ _).1 h3
  obtain ⟨r1, F4, c4, h4, k4⟩ := (bind_ok _ _ _ _ _).1 k3
  obtain ⟨y4, e6⟩ := (liftY_ok _ _ _ _ _ _).1 h4
  obtain ⟨_, F5, c5, h5, k5⟩ := (bind_ok _ _ _ _ _).1 k4
  obtain ⟨_, e7, e8⟩ := (takeSlots_ok _ _ _ _ _ _).1 h5
  obtain ⟨e9, e10, e11⟩ := (pure_ok _ _ _ _ _ _).1 k5
  subst e1 e2 e3 e4 e5 e6 e7 e8 e10 e11
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e9
  simp only [Bool.and_eq_true] at b1
  refine ⟨sent.toList, _, trRead_recvEs _ _ _ _ y2, y4, b1.1, b1.2, ?_, rfl, rfl⟩
  simpa using b3

/-- One round of a variable: the block's hearOne under the name "PSC round". -/
theorem roundIn_ok (form : RoundForm) (p p' : Psc) (z : E) (degree : Nat) (F G : Fork) (c c' : Ctx)
    (r : E) (h : roundIn form p z degree F c = .ok (((r, p'), G), c')) :
    ∃ w sent, form.weight z degree = some w ∧ p.ended = false ∧
      (hearOne "PSC round" .elems (w.d - 1) 0).Yields c (sent, r) c' ∧
      w.fits = true ∧ weightHeld w = true ∧ sent.length + 1 = w.d ∧
      p' = { p with claim := polyAt (w.complete sent p.claim) r, vars := p.vars.push w,
                    r := p.r.push r } ∧
      G = taken F (w.d - 1) := by
  unfold roundIn at h
  obtain ⟨_, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨b1, e1, e2⟩ := (must_ok _ _ _ _ _ _).1 h1
  obtain ⟨w, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨b2, e3, e4⟩ := (getS_ok _ _ _ _ _ _).1 h2
  subst e1 e2 e3 e4
  obtain ⟨sent, c3, y1, y2, a1, a2, a3, a4, a5⟩ := pscRound_ok _ _ _ _ _ _ _ _ _ k2
  refine ⟨w, sent, b2, by simpa using b1, ?_, a1, a2, a3, a4, a5⟩
  exact hearOne_of _ _ _ _ _ _ _ _ _ y1 (trAnswer_closeOne _ _ _ _ y2)

/-! ## Several rounds -/

/-- p' is p after the rounds rs under the weights ws. -/
structure Stepped (p p' : Psc) (ws : List Weight) (rs : List (List E × E)) : Prop where
  claim : p'.claim = claimAfter ws rs p.claim
  vars : p'.vars.toList = p.vars.toList ++ ws
  r : p'.r.toList = p.r.toList ++ rs.map (·.2)
  len : rs.length = ws.length
  sizes : ∀ x ∈ ws.zip rs, x.2.1.length + 1 = x.1.d
  held : ∀ w ∈ ws, w.fits = true ∧ weightHeld w = true
  start : p'.start = p.start
  target : p'.target = p.target
  eps : p'.eps = p.eps
  first : p'.first = p.first
  ended : p'.ended = p.ended
  rowMade : p'.rowMade = p.rowMade
  started : p'.started = p.started

theorem Stepped.nil (p : Psc) : Stepped p p [] [] :=
  ⟨rfl, by simp, by simp, rfl, by simp, by simp, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Stepped.cons (p p' : Psc) (w : Weight) (q : List E) (g : E) (ws : List Weight)
    (rs : List (List E × E)) (hf : w.fits = true) (hw : weightHeld w = true)
    (hq : q.length + 1 = w.d)
    (s : Stepped { p with claim := polyAt (w.complete q p.claim) g, vars := p.vars.push w,
                          r := p.r.push g } p' ws rs) :
    Stepped p p' (w :: ws) ((q, g) :: rs) where
  claim := by rw [s.claim]; rfl
  vars := by rw [s.vars]; simp
  r := by rw [s.r]; simp
  len := by simp [s.len]
  sizes := by
    intro x hx
    simp only [List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hq
    · exact s.sizes x hx
  held := by
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨hf, hw⟩
    · exact s.held v hv
  start := s.start
  target := s.target
  eps := s.eps
  first := s.first
  ended := s.ended
  rowMade := s.rowMade
  started := s.started

theorem hearMany_cons (n : Nat) (ns : List Nat) (a : List E × E) (l : List (List E × E))
    (c c1 c' : Ctx) (h1 : (hearOne "PSC round" .elems n 0).Yields c a c1)
    (h2 : (hearMany ns).Yields c1 l c') : (hearMany (n :: ns)).Yields c (a :: l) c' := by
  simp only [hearMany]
  exact (Blk.yields_bind _ _ _ _ _).2 ⟨a, c1, h1,
    (Blk.yields_bind _ _ _ _ _).2 ⟨l, c', h2, (Blk.yields_pure _ _ _ _).2 ⟨rfl, rfl⟩⟩⟩

theorem hearMany_nil (c : Ctx) : (hearMany []).Yields c [] c := by
  simp only [hearMany]
  exact (Blk.yields_pure _ _ _ _).2 ⟨rfl, rfl⟩

theorem eq2_weight (z : E) : RoundForm.weight .eq2 z 0 = some (Weight.equality z 3) := by
  simp [RoundForm.weight, RoundForm.degreeOK, RoundForm.equality, roundValues]

/-- The token sumcheck's rounds: one round under the equality weight of each coordinate. -/
theorem tscLoop_ok : ∀ (zs : List E) (r r' : Array E) (p p' : Psc) (F G : Fork) (c c' : Ctx),
    tscLoop zs r p F c = .ok (((r', p'), G), c') →
    ∃ rs, (hearMany (zs.map fun _ => 2)).Yields c rs c' ∧
      Stepped p p' (zs.map fun z => Weight.equality z 3) rs ∧
      r'.toList = r.toList ++ rs.map (·.2) ∧ G = taken F (2 * zs.length)
  | [], r, r', p, p', F, G, c, c', h => by
    simp only [tscLoop] at h
    obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
    subst e2 e3
    exact ⟨[], hearMany_nil _, Stepped.nil _, by simp, rfl⟩
  | z :: zs, r, r', p, p', F, G, c, c', h => by
    simp only [tscLoop] at h
    obtain ⟨⟨x, p1⟩, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
    obtain ⟨w, sent, b1, _, y1, a1, a2, a3, a4, a5⟩ := roundIn_ok _ _ _ _ _ _ _ _ _ _ h1
    rw [eq2_weight] at b1
    obtain rfl := Option.some.inj b1
    obtain ⟨rs, y2, s2, e2, e3⟩ := tscLoop_ok zs _ _ _ _ _ _ _ _ k1
    subst a4 a5
    refine ⟨(sent, x) :: rs, hearMany_cons _ _ _ _ _ _ _ y1 y2,
        Stepped.cons _ _ _ _ _ _ _ a1 a2 a3 s2,
      ?_, ?_⟩
    · rw [e2]; simp
    · rw [e3]
      show taken (taken F 2) (2 * zs.length) = taken F (2 * (zs.length + 1))
      rw [taken_taken, show 2 + 2 * zs.length = 2 * (zs.length + 1) by omega]

/-! ## The end: the round in Y and the end values -/

theorem atZero_d (n : Nat) : (Weight.atZero (n + 1)).d - 1 = n := by
  simp [Weight.atZero, Weight.equality]

/-- The end of a sumcheck with end values: the round "PSC Y" under the weight atZero, then the n end
values in a round "PSC values"; the values are put under the next n slots with the factor beta. -/
theorem pscEnds_ok (p p' : Psc) (degreeInY n : Nat) (F G : Fork) (c c' : Ctx) (e : Nat)
    (h : pscEnds p degreeInY n F c = .ok (((e, p'), G), c')) :
    ∃ sentY beta, ∃ v : Array E, ∃ c1 c2,
      (hearOne "PSC Y" .elems degreeInY 1).Yields c (sentY, beta) c1 ∧
      (Blk.recvEs n).Yields c1 v.toList c2 ∧ (Blk.closeEmpty "PSC values").Yields c2 () c' ∧
      v.size = n ∧ 1 ≤ degreeInY ∧ 1 ≤ n ∧ p.ended = false ∧
      sentY.length = degreeInY ∧
      p' = { p with claim := polyAt ((Weight.atZero (degreeInY + 1)).complete sentY p.claim) beta,
                    vars := p.vars.push (Weight.atZero (degreeInY + 1)), r := p.r.push beta,
                    ended := true } ∧
      e = F.next + degreeInY ∧
      (taken F (degreeInY + n)).hideRun e v beta = some G := by
  unfold pscEnds at h
  obtain ⟨_, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨b1, e1, e2⟩ := (must_ok _ _ _ _ _ _).1 h1
  rw [e1, e2] at k1
  obtain ⟨⟨beta, p1⟩, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨sentY, c3, y1, y2, _, _, a3, a4, a5⟩ := pscRound_ok _ _ _ _ _ _ _ _ _ h2
  rw [atZero_d] at y1 a5
  obtain ⟨v, F4, c4, h4, k4⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨y4, e4⟩ := (liftY_ok _ _ _ _ _ _).1 h4
  obtain ⟨_, F5, c5, h5, k5⟩ := (bind_ok _ _ _ _ _).1 k4
  obtain ⟨b5, e5, e6⟩ := (must_ok _ _ _ _ _ _).1 h5
  obtain ⟨_, F6, c6, h6, k6⟩ := (bind_ok _ _ _ _ _).1 k5
  obtain ⟨y6, e7⟩ := (liftY_ok _ _ _ _ _ _).1 h6
  obtain ⟨e', F7, c7, h7, k7⟩ := (bind_ok _ _ _ _ _).1 k6
  obtain ⟨e8, e9, e10⟩ := (takeSlots_ok _ _ _ _ _ _).1 h7
  obtain ⟨_, F8, c8, h8, k8⟩ := (bind_ok _ _ _ _ _).1 k7
  obtain ⟨b8, e11⟩ := (change_ok _ _ _ _ _ _).1 h8
  obtain ⟨e12, e13, e14⟩ := (pure_ok _ _ _ _ _ _).1 k8
  obtain ⟨e15, e16⟩ := Prod.mk.inj e12
  have hF7 : F7 = taken F (degreeInY + n) := by
    rw [e9, e7, e5, e4, a5, ← taken_taken]; rfl
  have he : e' = F.next + degreeInY := by
    rw [e8, e7, e5, e4, a5]; rfl
  rw [hF7, he, e13.symm] at b8
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at b1
  have hs : sentY.length = degreeInY := by
    have : sentY.length + 1 = degreeInY + 1 := a3
    omega
  rw [e6] at y6
  have hee : e = F.next + degreeInY := by rw [e15, he]
  rw [e14, e11, e10, hee]
  have g1 : (hearOne "PSC Y" .elems degreeInY 1).Yields c (sentY, beta) c2 :=
    hearOne_of "PSC Y" .elems degreeInY 1 sentY beta c c3 c2 y1
      (trAnswerNotZero_closeOne .pscY beta c3 c2 y2)
  have g2 : (Blk.recvEs n).Yields c2 v.toList c4 := trRead_recvEs n v c2 c4 y4
  have g3 : (Blk.closeEmpty "PSC values").Yields c4 () c6 := trEmpty_closeEmpty .pscValues c4 c6 y6
  have g4 : v.size = n := by simpa using b5
  have g5 : p' = { p with
      claim := polyAt ((Weight.atZero (degreeInY + 1)).complete sentY p.claim) beta,
      vars := p.vars.push (Weight.atZero (degreeInY + 1)), r := p.r.push beta, ended := true } := by
    rw [e16, a4]
  exact ⟨sentY, beta, v, c2, c4, g1, g2, g3, g4, b1.1.2, b1.2, b1.1.1, hs, g5, rfl, b8⟩

/-- The parts, put together: the block's own listener hears the whole sumcheck. -/
theorem hear_of (ds : List Nat) (dY n : Nat) (mu eps : E) (inX : List (List E × E))
    (inY : List E × E) (v : List E) (c c1 c2 c3 c4 c' : Ctx)
    (h1 : (hearOne "PSC epsilon" .join 1 0).Yields c ([mu], eps) c1)
    (h2 : (hearMany (ds.map (· - 1))).Yields c1 inX c2)
    (h3 : (hearOne "PSC Y" .elems dY 1).Yields c2 inY c3)
    (h4 : (Blk.recvEs n).Yields c3 v c4) (h5 : (Blk.closeEmpty "PSC values").Yields c4 () c') :
    (hear { degree := ds, withY := true, degreeY := dY, values := n }).Yields c
      ⟨mu, eps, inX ++ [inY], v⟩ c' := by
  unfold hear
  refine (Blk.yields_bind _ _ _ _ _).2 ⟨_, c1, h1, (Blk.yields_bind _ _ _ _ _).2 ⟨mu, c1,
    (Blk.yields_get _ _ _ _).2 ⟨rfl, rfl⟩, (Blk.yields_bind _ _ _ _ _).2 ⟨inX, c2, h2, ?_⟩⟩⟩
  simp only [if_true]
  exact (Blk.yields_bind _ _ _ _ _).2 ⟨inY, c3, h3, (Blk.yields_bind _ _ _ _ _).2 ⟨v, c4, h4,
    (Blk.yields_bind _ _ _ _ _).2 ⟨(), c', h5, (Blk.yields_pure _ _ _ _).2 ⟨rfl, rfl⟩⟩⟩⟩

end OnBytes.Model.Road
