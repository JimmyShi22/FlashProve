-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscTsc.lean: claimsIn and pscBegin on a run; from the shapes that the parts
of a sumcheck leave, the block's Psc.verify succeeds; the token sumcheck on the channel.

Main names:
  `ask_ok`: what a success of SubM.ask says.
  `claimsIn_ok`: n elements are received and nothing is closed. They are put under the next n slots
    with the factor 1.
  `pscBegin_ok`: the beginning at a form C: the target is the public part of C.
  `sumcheck_verify`: for a sumcheck whose first message holds mu alone, Psc.verify succeeds for any
    mask form, summand and slots of fitting sizes, and the model's running claim and walk are the
    block's claimAfter and hidingWalk.
  `tscIn_verify`: the token sumcheck (OnBytes/Model/Tsc.lean): one further scalar is received, then
    Psc.verify succeeds from the context behind it.
Limits: sumcheck_verify names none of the routines. Its hypotheses are the shapes that pscBegin_ok,
Stepped and pscEnds_ok give. One direction only, from a success of the model's routine. Nothing is
said on hiding.
-/
import OnBytes.Tie.Pv.Psc.Run.PscWhole

namespace OnBytes.Model.Road
open OnBytes.Psc (Weight hearOne hearMany hear claimAfter polyAt hidingWalk)

/-- What a success of SubM.ask says. -/
theorem ask_ok {α : Type} (f : Fork → Option α) (F G : Fork) (c c' : Ctx) (a : α) :
    SubM.ask f F c = .ok ((a, G), c') ↔ f F = some a ∧ G = F ∧ c' = c := by
  simp only [SubM.ask]
  cases f F with
  | none => simp [liftOption_none]
  | some y => simp [liftOption_some, eq_comm, and_assoc]

/-- Hidden values that ride in a message: n items are received; nothing is closed. -/
theorem claimsIn_ok (n : Nat) (F G : Fork) (c c' : Ctx) (j : Nat)
    (h : SubM.claimsIn n F c = .ok ((j, G), c')) :
    ∃ v : Array E, (Blk.recvEs n).Yields c v.toList c' ∧ v.size = n ∧ j = F.next ∧
      (taken F n).hideRun F.next v oneE = some G := by
  unfold SubM.claimsIn at h
  obtain ⟨v, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨y1, e1⟩ := (liftY_ok _ _ _ _ _ _).1 h1
  obtain ⟨_, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨b2, e2, e3⟩ := (must_ok _ _ _ _ _ _).1 h2
  obtain ⟨j1, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨e4, e5, e6⟩ := (takeSlots_ok _ _ _ _ _ _).1 h3
  obtain ⟨_, F4, c4, h4, k4⟩ := (bind_ok _ _ _ _ _).1 k3
  obtain ⟨b4, e7⟩ := (change_ok _ _ _ _ _ _).1 h4
  obtain ⟨e8, e9, e10⟩ := (pure_ok _ _ _ _ _ _).1 k4
  have hF3 : F3 = taken F n := by rw [e5, e2, e1]; rfl
  have hj : j1 = F.next := by rw [e4, e2, e1]
  rw [hF3, hj, ← e9] at b4
  have g1 : (Blk.recvEs n).Yields c v.toList c' := by
    rw [e10, e7, e6, e3]; exact trRead_recvEs n v c c1 y1
  exact ⟨v, g1, by simpa using b2, by rw [e8, hj], b4⟩

/-- The beginning at a claim C on hidden values: the target is the public part of C. -/
theorem pscBegin_ok (C : Aff) (F G : Fork) (c c' : Ctx) (p : Psc)
    (h : pscBegin C F c = .ok ((p, G), c')) :
    ∃ τ mu, F.publicPart C = some τ ∧
      (hearOne "PSC epsilon" .join 1 0).Yields c ([mu], p.eps) c' ∧
      p = { start := C, started := true, target := τ, first := F.next, eps := p.eps,
            claim := addE mu (mulE p.eps τ) } ∧
      G = taken F 1 := by
  unfold pscBegin at h
  obtain ⟨τ, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨b1, e1, e2⟩ := (ask_ok _ _ _ _ _ _).1 h1
  obtain ⟨p0, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  rw [e1, e2] at h2
  obtain ⟨mu, y, a1, a2⟩ := pscBeginAt_ok τ F F2 c c2 p0 h2
  obtain ⟨e3, e4, e5⟩ := (pure_ok _ _ _ _ _ _).1 k2
  have hp : p.eps = p0.eps := by rw [e3]
  refine ⟨τ, mu, b1, ?_, ?_, by rw [e4, a2]⟩
  · rw [e5, hp]; exact y
  · rw [hp, e3]
    conv => lhs; rw [a1]

/-- From the shapes. p0: as pscBegin_ok describes what pscBegin left; p1: after the rounds of the
variables; p2: as
pscEnds_ok describes what pscEnds left. -/
theorem sumcheck_verify (C : Aff) (τ mu : E) (first : Nat) (p0 p1 p2 : Psc) (ws : List Weight)
    (rs : List (List E × E)) (sentY : List E) (beta : E) (v : List E) (dY n : Nat)
    (c c1 c2 c3 c4 c' : Ctx)
    (hp0 : p0 = { start := C, started := true, target := τ, first := first, eps := p0.eps,
                  claim := addE mu (mulE p0.eps τ) })
    (h1 : (hearOne "PSC epsilon" .join 1 0).Yields c ([mu], p0.eps) c1)
    (h2 : (hearMany (ws.map fun w => w.d - 1)).Yields c1 rs c2) (s : Stepped p0 p1 ws rs)
    (h3 : (hearOne "PSC Y" .elems dY 1).Yields c2 (sentY, beta) c3)
    (h4 : (Blk.recvEs n).Yields c3 v c4) (h5 : (Blk.closeEmpty "PSC values").Yields c4 () c')
    (hY : sentY.length = dY) (hv : v.length = n) (d1 : 1 ≤ dY) (n1 : 1 ≤ n)
    (hp2 : p2 = { p1 with claim := polyAt ((Weight.atZero (dY + 1)).complete sentY p1.claim) beta,
                          vars := p1.vars.push (Weight.atZero (dY + 1)), r := p1.r.push beta,
                          ended := true })
    (m : MaskForm) (S : OnBytes.Psc.Summand) (fresh : List Slot) (hSn : S.shown = n)
    (hSd : S.degree = dY) (hf : fresh.length = OnBytes.Psc.masksOf ⟨ws, m, τ⟩ S)
    (ha : (S.coeffs ((rs.map (·.2)) ++ [beta] |>.take ws.length) v).length = 1 + S.kept) :
    ∃ o, (OnBytes.Psc.verify ⟨ws, m, τ⟩ S fresh).Yields c o c' ∧
      OnBytes.Psc.run ⟨ws, m, τ⟩ S fresh (heardOf mu p0.eps rs sentY beta v) = some o ∧
      p2.claim = claimAfter (OnBytes.Psc.varsOf ⟨ws, m, τ⟩ S) (rs ++ [(sentY, beta)])
        (addE mu (mulE p0.eps τ)) ∧
      p2.walk = hidingWalk ((OnBytes.Psc.varsOf ⟨ws, m, τ⟩ S).zip (rs.map (·.2) ++ [beta])) ∧
      p2.eps = p0.eps ∧ p2.target = τ ∧ p2.start = C ∧ p2.first = first := by
  subst hSn hSd
  obtain ⟨o, y, ho⟩ := verify_of ws m τ S fresh mu p0.eps beta rs sentY v c c1 c2 c3 c4 c' h1 h2 h3
      h4 h5
    s.len s.sizes (fun w hw => (s.held w hw).1) hY hv d1 n1 hf ha
  have hs0 : (S.shown == 0) = false := by
    cases hh : S.shown with
    | zero => omega
    | succ k => rfl
  have hvars : OnBytes.Psc.varsOf ⟨ws, m, τ⟩ S = ws ++ [Weight.atZero (S.degree + 1)] := by
    simp [OnBytes.Psc.varsOf, hs0]
  have c0 : p0.claim = addE mu (mulE p0.eps τ) := by conv => lhs; rw [hp0]
  have v0 : p0.vars.toList = [] := by rw [hp0]
  have r0 : p0.r.toList = [] := by rw [hp0]
  refine ⟨o, y, ho, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hvars, claimAfter_append ws rs _ _ _ s.len, hp2, ← c0, ← s.claim]
  · rw [hvars, hp2]
    unfold Psc.walk
    rw [zipT_eq]
    simp only [Array.toList_push, s.vars, s.r, v0, r0, List.nil_append]
  · rw [hp2]; exact s.eps
  · rw [hp2]; show p1.target = τ; rw [s.target, hp0]
  · rw [hp2]; show p1.start = C; rw [s.start, hp0]
  · rw [hp2]; show p1.first = first; rw [s.first, hp0]

/-- The token sumcheck, on the channel alone. One rider (the shown scalar of Cl), then a run of the
block's Psc.verify from the context behind the rider, at the equality weights of the first lt
coordinates of P. -/
theorem tscIn_verify (P : Array E) (lt shown degreeInY : Nat) (F G : Fork) (c c' : Ctx) (t : Tsc)
    (h : tscIn P lt shown degreeInY F c = .ok ((t, G), c')) :
    ∃ (rider : Array E) (c1 : Ctx) (F1 : Fork) (τ mu eps : E) (rs : List (List E × E))
      (sentY : List E) (beta : E) (v : Array E),
      (Blk.recvEs 1).Yields c rider.toList c1 ∧ rider.size = 1 ∧ lt ≤ P.size ∧
      t.sCl = F.next ∧ (taken F 1).hideRun F.next rider oneE = some F1 ∧
      F1.publicPart (Aff.slot F.next) = some τ ∧
      t.sEnd = F1.next + 1 + 2 * (P.toList.take lt).length + degreeInY ∧
      t.r.toList = rs.map (·.2) ∧
      ∀ (m : MaskForm) (S : OnBytes.Psc.Summand) (fresh : List Slot), S.shown = shown →
        S.degree = degreeInY →
        fresh.length = OnBytes.Psc.masksOf ⟨(P.toList.take lt).map fun z => Weight.equality z 3, m,
            τ⟩ S →
        (S.coeffs ((rs.map (·.2)) ++ [beta] |>.take
          ((P.toList.take lt).map fun z => Weight.equality z 3).length) v.toList).length = 1 +
              S.kept →
        ∃ o, (OnBytes.Psc.verify ⟨(P.toList.take lt).map fun z => Weight.equality z 3, m, τ⟩ S
              fresh).Yields c1 o c' ∧
          OnBytes.Psc.run ⟨(P.toList.take lt).map fun z => Weight.equality z 3, m, τ⟩ S fresh
            (heardOf mu eps rs sentY beta v.toList) = some o ∧
          t.p.claim = claimAfter
            (OnBytes.Psc.varsOf ⟨(P.toList.take lt).map fun z => Weight.equality z 3, m, τ⟩ S)
            (rs ++ [(sentY, beta)]) (addE mu (mulE eps τ)) ∧
          t.p.walk = hidingWalk
            ((OnBytes.Psc.varsOf ⟨(P.toList.take lt).map fun z => Weight.equality z 3, m, τ⟩ S).zip
              (rs.map (·.2) ++ [beta])) ∧
          t.p.eps = eps ∧ t.p.target = τ ∧ t.p.start = Aff.slot F.next ∧ t.p.first = F1.next := by
  unfold tscIn at h
  obtain ⟨o1, F2, c2, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨⟨sEnd, p2⟩, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k3
  unfold tscRounds at h1
  obtain ⟨_, Fa, ca, ha, ka⟩ := (bind_ok _ _ _ _ _).1 h1
  obtain ⟨ba, ea1, ea2⟩ := (must_ok _ _ _ _ _ _).1 ha
  rw [ea1, ea2] at ka
  obtain ⟨sCl, Fb, cb, hb, kb⟩ := (bind_ok _ _ _ _ _).1 ka
  obtain ⟨rider, yb, sb, jb, Hb⟩ := claimsIn_ok 1 F Fb c cb sCl hb
  obtain ⟨p0, Fc, cc, hc, kc⟩ := (bind_ok _ _ _ _ _).1 kb
  obtain ⟨τ, mu, pc, yc, hp0, Gc⟩ := pscBegin_ok _ Fb Fc cb cc p0 hc
  obtain ⟨⟨r1, p1⟩, Fd, cd, hd, kd⟩ := (bind_ok _ _ _ _ _).1 kc
  obtain ⟨rs, yd, sd, rd1, Gd⟩ := tscLoop_ok _ _ _ _ _ _ _ _ _ hd
  obtain ⟨ee1, ee2, ee3⟩ := (pure_ok _ _ _ _ _ _).1 kd
  have ho1p : o1.p = p1 := by rw [ee1]
  rw [ho1p, ee2, ee3] at h3
  obtain ⟨sentY, beta, v, c5, c6, y5, y6, y7, sv, d1, n1, _, sY, hp2, hE, _⟩ :=
    pscEnds_ok p1 p2 degreeInY shown Fd F3 cd c3 sEnd h3
  rw [jb] at pc hp0
  refine ⟨rider, cb, Fb, τ, mu, p0.eps, rs, sentY, beta, v, yb, sb, by simpa using ba, ?_, Hb, pc,
      ?_, ?_,
    ?_⟩
  · rw [e1, ee1]; exact jb
  · rw [e1]
    show sEnd = _
    rw [hE, Gd, Gc]
    simp only [taken]
  · rw [e1, ee1]
    show r1.toList = _
    rw [rd1]; rfl
  · intro m S fresh hSn hSd hf ha'
    have hm : ((P.toList.take lt).map fun z => Weight.equality z 3).map (fun w => w.d - 1) =
        (P.toList.take lt).map fun _ => 2 := by
      rw [List.map_map]; rfl
    have htp : t.p = p2 := by rw [e1]
    rw [htp, e3]
    exact sumcheck_verify (Aff.slot F.next) τ mu Fb.next p0 p1 p2 _ rs sentY beta v.toList degreeInY
        shown
      cb cc cd c5 c6 c3 hp0 yc (by rw [hm]; exact yd) sd y5 y6 y7 sY (by simpa using sv) d1 n1 hp2
      m S fresh hSn hSd hf ha'

#print axioms tscIn_verify
#print axioms sumcheck_verify

end OnBytes.Model.Road
