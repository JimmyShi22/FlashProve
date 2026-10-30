-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5SaidAll.lean: kind K5: what the whole hearing has heard where it returns.

Main names:
  `Lists`, `Lists.rounds`: the lists that the stretch's rounds hold, stage by stage; the same, round
    by round.
  `SumAt`: a sumcheck's SumSaid (Att/K5Said.lean), seen from a ledger behind the hearing.
  `Said x h G L`: every field of the record Heard, and every number that it names in the ledger G,
    in
    the lists L: which scalar lies under which number with which factor; each sumcheck's record;
      each
    start form's public part, read.
  `hear_said`: where hear x returns from a ledger whose arrays have their length, there are lists L
    such that the rounds used up hold just L and Said x h G L. The rounds fix L.

Premise: Sized F. It is a fact that the fold must carry; not shown in this file or in what it
imports.
Sources: what Att/K5Said.lean names, and OnBytes/Tie/Pv/Att/HearSaid.lean (SameRead, SumRead,
slot_read, sum_read); OnBytes/Model/AttentionDivide.lean (weightedSum: K5P's batched is it by
unfolding).
Limits: one direction, from a return.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5Said

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (PscH Lies SameRead SumRead slot_read sum_read)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)

/-! ## The lists -/

/-- The lists that the stretch's rounds hold. -/
structure Lists where
  /-- for each remainder unit its three scalars -/
  planes : List (List E)
  /-- for each softmax-table unit its seven scalars and its sumcheck -/
  units : List (List E × PscH)
  v5 : List E
  vI : List E
  v2 : List E
  HE : PscH
  xV : E
  vC : List E
  HM : PscH
  HVD : PscH
  pt : List E
  vM : List E
  xF : E
  HF : PscH
  xD : E
  HD : PscH
  xH : E
  HH : PscH

/-- A sumcheck's rounds. -/
def sumRounds (riders : List E) (H : PscH) : List RoundH := partsRounds riders H.mu H.eps H.rs H.sentY H.beta H.v

/-- The units' rounds. pre: the scalars that wait in front of the first. -/
def unitsRounds : List E → List (List E × PscH) → List RoundH
  | _, [] => []
  | pre, (v7, H) :: l => sumRounds (pre ++ v7) H ++ unitsRounds [] l

/-- The scalars that still wait behind the units. -/
def leftOf (pre : List E) : List (List E × PscH) → List E
  | [] => pre
  | _ :: _ => []

theorem leftOf_nil : ∀ l : List (List E × PscH), leftOf [] l = []
  | [] => rfl
  | _ :: _ => rfl

/-- The riders of the sumcheck «denominator × output». -/
def Lists.ridersE (L : Lists) : List E := leftOf L.planes.flatten L.units ++ (L.v5 ++ (L.vI ++ L.v2))

/-- **The lists, round by round.** -/
def Lists.rounds (L : Lists) : List RoundH :=
  unitsRounds L.planes.flatten L.units ++ (sumRounds L.ridersE L.HE ++ (([], some [L.xV]) ::
    (sumRounds L.vC L.HM ++ (sumRounds [] L.HVD ++ (([], some L.pt) :: (L.vM, some [L.xF]) ::
      (sumRounds [] L.HF ++ (([], some [L.xD]) :: (sumRounds [] L.HD ++ (([], some [L.xH]) ::
        sumRounds [] L.HH)))))))))

/-! ## Seen from the ledger behind -/

/-- n scalars lie under the numbers from j on, each with the factor 1. -/
def PutRun (G : Fork) (j : Nat) (v : List E) : Prop := ∀ i, i < v.length → Put G (j + i) (v.getD i zeroE) oneE

theorem PutRun.mono {G G' : Fork} {j : Nat} {v : List E} (h : PutRun G j v) (s : Stays G G') : PutRun G' j v :=
  fun i hi => s _ _ _ (h i hi)

/-- A sumcheck, seen from the ledger Gf. -/
def SumAt (C : Aff) (st : Stage) (pre : List E) (H : PscH) (hh : MaskedSum.Heard) (Gf : Fork) : Prop :=
  ∃ vs e F G used, st = .sum vs e ∧ SumSaid C vs e F G pre H used hh ∧ Stays G Gf

theorem SumAt.mono {C : Aff} {st : Stage} {pre : List E} {H : PscH} {hh : MaskedSum.Heard} {G G' : Fork}
    (h : SumAt C st pre H hh G) (s : Stays G G') : SumAt C st pre H hh G' := by
  obtain ⟨vs, e, F, G0, used, a, b, c⟩ := h
  exact ⟨vs, e, F, G0, used, a, b, c.trans s⟩

/-- The remainder units' scalars. -/
def PlanesAt : List Nat → List (List E) → Fork → Prop
  | [], [], _ => True
  | j :: js, v :: vs, G => v.length = 3 ∧ PutRun G j v ∧ PlanesAt js vs G
  | _, _, _ => False

theorem PlanesAt.mono {G G' : Fork} (s : Stays G G') : ∀ {js : List Nat} {vs : List (List E)},
    PlanesAt js vs G → PlanesAt js vs G'
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨a, b, c⟩ => ⟨a, b.mono s, PlanesAt.mono s c⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- The softmax-table units. -/
def UnitsAt : List (Nat × Nat) → List (Nat × MaskedSum.Heard) → List E → List (List E × PscH) → Fork → Prop
  | [], [], _, [], _ => True
  | u :: us, o :: os, pre, (v7, H) :: l, G =>
    v7.length = 7 ∧ PutRun G o.1 v7 ∧ SumAt (.slot (o.1 + 6)) (products u.1 u.2) (pre ++ v7) H o.2 G ∧
      SameRead o.2.target (v7.getD 6 zeroE) ∧ UnitsAt us os [] l G
  | _, _, _, _, _ => False

theorem UnitsAt.mono {G G' : Fork} (s : Stays G G') : ∀ {us : List (Nat × Nat)} {os : List (Nat × MaskedSum.Heard)}
    {pre : List E} {l : List (List E × PscH)}, UnitsAt us os pre l G → UnitsAt us os pre l G'
  | [], [], _, [], _ => trivial
  | _ :: _, _ :: _, _, (_, _) :: _, ⟨a, b, c, d, e⟩ => ⟨a, b.mono s, c.mono s, d, UnitsAt.mono s e⟩
  | [], [], _, _ :: _, h => h.elim
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | _ :: _, _ :: _, _, [], h => h.elim

/-- **What the record Heard holds, in the lists.** G: the ledger behind the hearing. -/
structure Said (x : Params.AttentionRounds) (h : Heard) (G : Fork) (L : Lists) : Prop where
  planes : PlanesAt h.remainders.toList L.planes G
  nPlanes : L.planes.length = x.planeMessages
  units : UnitsAt x.score h.scores.toList L.planes.flatten L.units G
  l5 : L.v5.length = 5
  p5 : PutRun G h.five L.v5
  lI : L.vI.length = x.lt
  pI : PutRun G h.bits L.vI
  l2 : L.v2.length = 2
  p2 : PutRun G h.two L.v2
  sE : SumAt (.slot (h.five + 1)) (products x.e x.pairs) L.ridersE L.HE h.division G
  tE : SameRead h.division.target (L.v5.getD 1 zeroE)
  gam : h.gam = (MaskedSum.powersFrom L.xV 2 oneE).toArray
  lC : L.vC.length = 2
  pC : PutRun G h.values L.vC
  sM : SumAt (.slot h.values) (products x.valueM x.pairs) L.vC L.HM h.below G
  tM : SameRead h.below.target (L.vC.getD 0 zeroE)
  sVD : SumAt (.slot (h.values + 1)) (products x.valueD x.pairs) [] L.HVD h.on G
  tVD : SameRead h.on.target (L.vC.getD 1 zeroE)
  point : h.point = L.pt.toArray
  lPt : L.pt.length = 2 * x.lgk + 2 * x.lt + 4
  lM : L.vM.length = x.pairs
  pM : PutRun G h.maxima L.vM
  om : h.om = (MaskedSum.powersFrom L.xF x.pairs oneE).toArray
  sF : SumAt (batched x.pairs h.om h.maxima 1 0) (products x.attained x.pairs) [] L.HF h.atIndex G
  tF : SumRead h.atIndex.target x.pairs h.om fun b => L.vM.getD b zeroE
  om' : h.om' = (MaskedSum.powersFrom L.xD x.pairs oneE).toArray
  sD : SumAt (batched x.pairs h.om' h.atIndex.sEnd 2 1) (keyStage x) [] L.HD h.key G
  tD : SumRead h.key.target x.pairs h.om' fun b => L.HF.v.getD (2 * b + 1) zeroE
  om'' : h.om'' = (MaskedSum.powersFrom L.xH x.pairs oneE).toArray
  sH : SumAt (.ofConst zeroE) (products x.bits x.pairs) [] L.HH h.cells G
  tH : h.cells.target = zeroE

/-! ## The pieces -/

theorem takes_said : ∀ (k : Nat) (js : List Nat) (F G : Fork) (rs rs' : List Fmt.RoundView) (lead lead' : Nat) (pre : List E),
    TakesRan 3 k js (F, rs, lead) (G, rs', lead') → Sized F → Open rs lead pre →
    ∃ vs : List (List E), vs.length = k ∧ rs' = rs ∧ Open rs' lead' (pre ++ vs.flatten) ∧ Sized G ∧ Stays F G ∧
      PlanesAt js vs G
  | 0, [], F, G, rs, rs', lead, lead', pre, h, hz, ho => by
    have e : (G, rs', lead') = (F, rs, lead) := h
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1, e2, e3⟩ := e
    subst e1 e2 e3
    exact ⟨[], rfl, rfl, by simpa using ho, hz, Stays.refl _, trivial⟩
  | k + 1, j :: js, F, G, rs, rs', lead, lead', pre, ⟨⟨F1, rs1, l1⟩, h1, h2⟩, hz, ho => by
    obtain ⟨v, a1, a2, a3, a4, a5, a6, a7, _⟩ := take_said h1 hz ho
    obtain ⟨vs, b1, b2, b3, b4, b5, b6⟩ := takes_said k js F1 G rs1 rs' l1 lead' (pre ++ v) h2 a5 a3
    refine ⟨v :: vs, by rw [List.length_cons, b1], by rw [b2, a2], ?_, b4, a6.trans b5, a1, ?_, b6⟩
    · rw [List.flatten_cons, ← List.append_assoc]
      exact b3
    · intro i hi
      exact b5 _ _ _ (a7 i (by rw [← a1]; exact hi))
  | 0, _ :: _, _, _, _, _, _, _, _, h, _, _ => h.elim
  | _ + 1, [], _, _, _, _, _, _, _, h, _, _ => h.elim

theorem units_said : ∀ (us : List (Nat × Nat)) (os : List (Nat × MaskedSum.Heard)) (F G : Fork)
    (rs rs' : List Fmt.RoundView) (lead lead' : Nat) (pre : List E),
    UnitsRan us os (F, rs, lead) (G, rs', lead') → Sized F → Open rs lead pre →
    ∃ (l : List (List E × PscH)) (used : List Fmt.RoundView), rs = used ++ rs' ∧ RoundsAre (unitsRounds pre l) used ∧
      Open rs' lead' (leftOf pre l) ∧ Sized G ∧ Stays F G ∧ UnitsAt us os pre l G
  | [], [], F, G, rs, rs', lead, lead', pre, h, hz, ho => by
    have e : (G, rs', lead') = (F, rs, lead) := h
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1, e2, e3⟩ := e
    subst e1 e2 e3
    exact ⟨[], [], rfl, trivial, ho, hz, Stays.refl _, trivial⟩
  | u :: us, o :: os, F, G, rs, rs', lead, lead', pre, ⟨⟨F2, rs2, l2⟩, ⟨⟨F1, rs1, l1⟩, h1, h2⟩, h3⟩, hz, ho => by
    obtain ⟨v7, a1, a2, a3, a4, a5, a6, a7, _⟩ := take_said h1 hz ho
    obtain ⟨b1, H, used, b2, b3⟩ := sum_said h2 a5 a3
    subst b1
    obtain ⟨l, used', c1, c2, c3, c4, c5, c6⟩ :=
      units_said us os F2 G rs2 rs' 0 lead' [] h3 b3.sized (open_zero _)
    refine ⟨(v7, H) :: l, used ++ used', by rw [← a2, b2, c1, List.append_assoc], RoundsAre.append b3.rounds c2,
      by rw [leftOf_nil] at c3; exact c3, c4, a6.trans (b3.stays.trans c5), a1, ?_, ⟨_, _, F1, F2, used, rfl, b3, c5⟩,
      slot_read (a7 6 (by omega)).lies b3.target, c6⟩
    intro i hi
    exact c5 _ _ _ (b3.stays _ _ _ (a7 i (by rw [← a1]; exact hi)))
  | [], _ :: _, _, _, _, _, _, _, _, h, _, _ => h.elim
  | _ :: _, [], _, _, _, _, _, _, _, h, _, _ => h.elim

/-! ## The whole -/

theorem putRun_of {G : Fork} {j n : Nat} {v : List E} (hl : v.length = n)
    (h : ∀ i, i < n → Put G (j + i) (v.getD i zeroE) oneE) : PutRun G j v := fun i hi => h i (by rw [← hl]; exact hi)

/-- **Where the hearing returns.** -/
theorem hear_said {x : Params.AttentionRounds} {F G : Fork} {rs rest : List Fmt.RoundView} {lead : Nat} {h : Heard}
    (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : Sized F) :
    ∃ (L : Lists) (used : List Fmt.RoundView), rs = used ++ rest ∧ RoundsAre L.rounds used ∧ Said x h G L ∧ Sized G ∧
      Stays F G := by
  obtain ⟨⟨Fa, rsa, la⟩, ⟨Fb, rsb, lb⟩, ⟨F1, rs1, l1⟩, ⟨F2, rs2, l2⟩, ⟨F3, rs3, l3⟩, ⟨F4, rs4, l4⟩, ⟨F5, rs5, l5⟩,
    ⟨F6, rs6, l6⟩, ⟨F7, rs7, l7⟩, ⟨F8, rs8, l8⟩, ⟨F9, rs9, l9⟩, ⟨F10, rs10, l10⟩, ⟨F11, rs11, l11⟩, ⟨F12, rs12, l12⟩,
    ⟨F13, rs13, l13⟩, ⟨F14, rs14, l14⟩, ⟨F15, rs15, l15⟩, pt, ha, hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, hpt, h10,
    h11, h12, h13, h14, h15, h16⟩ := (hear_ran hh).ran
  obtain ⟨planes, pa1, pa2, pa3, pa4, pa5, pa6⟩ := takes_said _ _ _ _ _ _ _ _ [] ha hz (open_zero _)
  rw [List.nil_append] at pa3
  obtain ⟨units, usedU, ub1, ub2, ub3, ub4, ub5, ub6⟩ := units_said _ _ _ _ _ _ _ _ _ hb pa4 pa3
  obtain ⟨v5, a1, a2, a3, a4, a5, a6, a7, _⟩ := take_said h1 ub4 ub3
  obtain ⟨vI, b1, b2, b3, b4, b5, b6, b7, _⟩ := take_said h2 a5 a3
  obtain ⟨v2, c1, c2, c3, c4, c5, c6, c7, _⟩ := take_said h3 b5 b3
  rw [List.append_assoc, List.append_assoc] at c3
  obtain ⟨d0, HE, usedE, d1, d2⟩ := sum_said h4 c5 c3
  subst d0
  obtain ⟨e1, e0, r5, xV, e2, e3, e4⟩ := batch_said h5 (open_zero _)
  subst e0 e1
  obtain ⟨vC, f1, f2, f3, f4, f5, f6, f7, _⟩ := take_said h6 d2.sized (open_zero _)
  rw [List.nil_append] at f3
  obtain ⟨g0, HM, usedM, g1, g2⟩ := sum_said h7 f5 f3
  subst g0
  obtain ⟨i0, HVD, usedVD, i1, i2⟩ := sum_said h8 g2.sized (open_zero _)
  subst i0
  obtain ⟨j1, j0, j2, r9, j3, j4⟩ := close_said h9 (open_zero _)
  subst j0 j1
  obtain ⟨vM, k1, k2, k3, k4, k5, k6, k7, _⟩ := take_said h10 i2.sized (open_zero _)
  rw [List.nil_append] at k3
  obtain ⟨m1, m0, r11, xF, m2, m3, m4⟩ := batch_said h11 k3
  subst m0 m1
  obtain ⟨n0, HF, usedF, n1, n2⟩ := sum_said h12 k5 (open_zero _)
  subst n0
  obtain ⟨o1, o0, r13, xD, o2, o3, o4⟩ := batch_said h13 (open_zero _)
  subst o0 o1
  obtain ⟨p0, HD, usedD, p1, p2⟩ := sum_said h14 n2.sized (open_zero _)
  subst p0
  obtain ⟨q1, q0, r15, xH, q2, q3, q4⟩ := batch_said h15 (open_zero _)
  subst q0 q1
  obtain ⟨_, HH, usedH, s1, s2⟩ := sum_said h16 p2.sized (open_zero _)
  -- what stays, from each ledger to the last
  have K14 : Stays F15 G := s2.stays
  have K12 : Stays F13 G := p2.stays.trans K14
  have K10 : Stays F11 G := n2.stays.trans K12
  have K8 : Stays F9 G := k6.trans K10
  have K7 : Stays F7 G := i2.stays.trans K8
  have K6 : Stays F6 G := g2.stays.trans K7
  have K4 : Stays F5 G := f6.trans K6
  have K3 : Stays F3 G := d2.stays.trans K4
  have K2 : Stays F2 G := c6.trans K3
  have K1 : Stays F1 G := b6.trans K2
  have Kb : Stays Fb G := a6.trans K1
  have Ka : Stays Fa G := ub5.trans Kb
  refine ⟨⟨planes, units, v5, vI, v2, HE, xV, vC, HM, HVD, pt, vM, xF, HF, xD, HD, xH, HH⟩,
    usedU ++ (usedE ++ (r5 :: (usedM ++ (usedVD ++ (r9 :: r11 :: (usedF ++ (r13 :: (usedD ++ (r15 :: usedH))))))))),
    ?_, ?_, ?_, s2.sized, pa5.trans Ka⟩
  · rw [← pa2, ub1, ← a2, ← b2, ← c2, d1, e2, ← f2, g1, i1, j3, ← k2, m2, n1, o2, p1, q2, s1]
    simp only [List.append_assoc, List.cons_append]
  · exact RoundsAre.append ub2 (RoundsAre.append d2.rounds ⟨e3, RoundsAre.append g2.rounds
      (RoundsAre.append i2.rounds ⟨j4, m3, RoundsAre.append n2.rounds ⟨o3, RoundsAre.append p2.rounds
        ⟨q3, s2.rounds⟩⟩⟩)⟩)
  · exact
      { planes := pa6.mono Ka
        nPlanes := pa1
        units := ub6.mono Kb
        l5 := a1
        p5 := (putRun_of a1 a7).mono K1
        lI := b1
        pI := (putRun_of b1 b7).mono K2
        l2 := c1
        p2 := (putRun_of c1 c7).mono K3
        sE := ⟨_, _, F3, F5, usedE, rfl, d2, K4⟩
        tE := slot_read (c6 _ _ _ (b6 _ _ _ (a7 1 (by omega)))).lies d2.target
        gam := e4
        lC := f1
        pC := (putRun_of f1 f7).mono K6
        sM := ⟨_, _, F6, F7, usedM, rfl, g2, K7⟩
        tM := slot_read (by simpa using (f7 0 (by omega)).lies) g2.target
        sVD := ⟨_, _, F7, F9, usedVD, rfl, i2, K8⟩
        tVD := slot_read (g2.stays _ _ _ (f7 1 (by omega))).lies i2.target
        point := hpt
        lPt := j2
        lM := k1
        pM := (putRun_of k1 k7).mono K10
        om := m4
        sF := ⟨_, _, F11, F13, usedF, rfl, n2, K12⟩
        tF := sum_read (s := fun b => h.maxima + (1 * b + 0)) (fun b hb => by
          have := (k7 b hb).lies
          simpa using this) n2.target
        om' := o4
        sD := ⟨_, _, F13, F15, usedD, rfl, p2, K14⟩
        tD := sum_read (s := fun b => h.atIndex.sEnd + (2 * b + 1)) (fun b hb => (n2.ends (2 * b + 1) (by
          show 2 * b + 1 < 2 * x.pairs
          omega)).lies) p2.target
        om'' := q4
        sH := ⟨_, _, F15, G, usedH, rfl, s2, Stays.refl _⟩
        tH := by
          have := s2.target
          simp only [Fork.publicPart, Aff.ofConst] at this
          exact (Option.some.inj this).symm }

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.sum_said
#print axioms VerifiableInference.Desc.First.Att.P.hear_said
