-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05One.lean: the rounds fix the lists, and the ties fix the data. Two records
of lists that the same
rounds hold (RoundsAre L.rounds rs, RoundsAre L'.rounds rs), each with Said at one plan that has a
unit, are one; two typed
data with the four ties are one. So at each view there is one record of lists and one typed
transcript.

Main names:
  `holds_one`, `round_one`: what a round holds, and what it drew, are fixed by the round.
  `mid_one`, `sum_one`: a masked sumcheck's rounds fix its riders and its six lists, where the
    numbers of variables
    agree. `sumAt_rs`: a sumcheck has heard as many variables' rounds as its stage has variables.
  `units_one`, `planes_len`, `flatten_one`, `left_nil`.
  `lists_one`: the rounds fix the lists.
  `sumH_one`, `tailH_one`, `unitsH_one`: two typed data with the four ties (UnitsOfP, TailOfP, and
    the values' ties
    UnitsVals, TailVals) are one.

Sources: what Att/K5SaidAll.lean and Att/K5Claims.lean name.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (PscH)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)

theorem holds_one {r : Fmt.RoundView} {l l' : List E} (h : Holds r l) (h' : Holds r l') : l = l' := by
  have e : l.map (fun x => Fmt.ItemValue.e x.triple) = l'.map fun x => Fmt.ItemValue.e x.triple := h.symm.trans h'
  refine List.map_injective_iff.2 (fun a b hab => ?_) e
  have h1 : a.triple = b.triple := by injection hab
  rw [← E.ofTriple_triple a, h1, E.ofTriple_triple]

/-- A round that drew, heard twice. -/
theorem round_one {r : Fmt.RoundView} {s s' d d' : List E} (h : IsRound r (s, some d)) (h' : IsRound r (s', some d')) :
    s = s' ∧ d = d' :=
  ⟨holds_one h.1 h'.1, (h.2 _ rfl).trans (h'.2 _ rfl).symm⟩

theorem mid_one {y y' z z' : RoundH} {t t' : List RoundH} : ∀ (a a' : List (List E × E)) (rs : List Fmt.RoundView),
    a.length = a'.length →
    RoundsAre ((a.map fun x => ((x.1, some [x.2]) : RoundH)) ++ (y :: z :: t)) rs →
    RoundsAre ((a'.map fun x => ((x.1, some [x.2]) : RoundH)) ++ (y' :: z' :: t')) rs →
    a = a' ∧ ∃ rs2, RoundsAre (y :: z :: t) rs2 ∧ RoundsAre (y' :: z' :: t') rs2
  | [], [], rs, _, h, h' => ⟨rfl, rs, h, h'⟩
  | x :: a, x' :: a', r :: rs, hl, ⟨h1, h2⟩, ⟨h1', h2'⟩ => by
    obtain ⟨e1, e2⟩ := round_one h1 h1'
    obtain ⟨e3, q⟩ := mid_one a a' rs (by simpa using hl) h2 h2'
    have e4 : x.2 = x'.2 := by simpa using e2
    exact ⟨by rw [e3, Prod.ext e1 e4], q⟩
  | _ :: _, _ :: _, [], _, h, _ => h.elim
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl

/-- **A masked sumcheck's rounds fix its riders and its lists.** -/
theorem sum_one {r r' : List E} {H H' : PscH} {t t' : List RoundH} {rs : List Fmt.RoundView}
    (hl : H.rs.length = H'.rs.length) (h : RoundsAre (sumRounds r H ++ t) rs)
    (h' : RoundsAre (sumRounds r' H' ++ t') rs) :
    r = r' ∧ H = H' ∧ ∃ rs2, RoundsAre t rs2 ∧ RoundsAre t' rs2 := by
  rcases rs with _ | ⟨r0, rs⟩
  · exact h.elim
  have h0 : RoundsAre ((H.rs.map fun x => ((x.1, some [x.2]) : RoundH)) ++
      ((H.sentY, some [H.beta]) :: (H.v, none) :: t)) rs := by
    have := h.2
    simpa [List.append_assoc] using this
  have h0' : RoundsAre ((H'.rs.map fun x => ((x.1, some [x.2]) : RoundH)) ++
      ((H'.sentY, some [H'.beta]) :: (H'.v, none) :: t')) rs := by
    have := h'.2
    simpa [List.append_assoc] using this
  obtain ⟨a1, a2⟩ := round_one h.1 h'.1
  obtain ⟨b1, rs2, b2, b3⟩ := mid_one _ _ rs hl h0 h0'
  rcases rs2 with _ | ⟨rY, _ | ⟨rv, rs3⟩⟩
  · exact b2.elim
  · exact b2.2.elim
  obtain ⟨c1, c2⟩ := round_one b2.1 b3.1
  have c3 : H.v = H'.v := holds_one b2.2.1.1 b3.2.1.1
  have d1 := List.append_inj' a1 rfl
  have e1 : H.mu = H'.mu := by simpa using d1.2
  have e2 : H.eps = H'.eps := by simpa using a2
  have e3 : H.beta = H'.beta := by simpa using c2
  refine ⟨d1.1, ?_, rs3, b2.2.2, b3.2.2⟩
  obtain ⟨mu, eps, rs', sY, be, v⟩ := H
  obtain ⟨mu', eps', rs'', sY', be', v'⟩ := H'
  simp only at e1 e2 e3 b1 c1 c3
  subst e1 e2 e3 b1 c1 c3
  rfl

/-- A sumcheck has heard as many variables' rounds as its stage has variables. -/
theorem sumAt_rs {C : Aff} {vs : List Var} {e : Ends} {pre : List E} {H : PscH} {hh : MaskedSum.Heard} {G : Fork}
    (h : SumAt C (.sum vs e) pre H hh G) : H.rs.length = vs.length := by
  obtain ⟨vs', e', _, _, _, e1, sd, _⟩ := h
  injection e1 with e2 _
  subst e2
  simpa using congrArg List.length sd.lens

theorem units_one {G G' : Fork} {t t' : List RoundH} : ∀ (ps : List (ℕ × ℕ)) (os os' : List (ℕ × MaskedSum.Heard))
    (pre pre' : List E) (l l' : List (List E × PscH)) (rs : List Fmt.RoundView), UnitsAt ps os pre l G →
    UnitsAt ps os' pre' l' G' → RoundsAre (unitsRounds pre l ++ t) rs → RoundsAre (unitsRounds pre' l' ++ t') rs →
    (ps ≠ [] → pre = pre') ∧ l = l' ∧ ∃ rs2, RoundsAre t rs2 ∧ RoundsAre t' rs2 := by
  intro ps
  induction ps with
  | nil =>
    intro os os' pre pre' l l' rs a b h h'
    rcases os with _ | ⟨o, os⟩ <;> rcases l with _ | ⟨x, l⟩ <;> simp [UnitsAt] at a
    rcases os' with _ | ⟨o', os'⟩ <;> rcases l' with _ | ⟨x', l'⟩ <;> simp [UnitsAt] at b
    exact ⟨fun hn => absurd rfl hn, rfl, rs, h, h'⟩
  | cons p ps ih =>
    intro os os' pre pre' l l' rs a b h h'
    rcases os with _ | ⟨o, os⟩
    · cases l <;> simp [UnitsAt] at a
    rcases l with _ | ⟨⟨v7, H⟩, l⟩
    · simp [UnitsAt] at a
    rcases os' with _ | ⟨o', os'⟩
    · cases l' <;> simp [UnitsAt] at b
    rcases l' with _ | ⟨⟨v7', H'⟩, l'⟩
    · simp [UnitsAt] at b
    obtain ⟨a1, _, a3, _, a5⟩ := a
    obtain ⟨b1, _, b3, _, b5⟩ := b
    have h1 : RoundsAre (sumRounds (pre ++ v7) H ++ (unitsRounds [] l ++ t)) rs := by
      simpa [unitsRounds, List.append_assoc] using h
    have h1' : RoundsAre (sumRounds (pre' ++ v7') H' ++ (unitsRounds [] l' ++ t')) rs := by
      simpa [unitsRounds, List.append_assoc] using h'
    obtain ⟨e1, e2, rs2, c1, c2⟩ := sum_one (by rw [sumAt_rs a3, sumAt_rs b3]) h1 h1'
    obtain ⟨_, e3, q⟩ := ih os os' [] [] l l' rs2 a5 b5 c1 c2
    have d := List.append_inj' e1 (by rw [a1, b1])
    exact ⟨fun _ => d.1, by rw [d.2, e2, e3], q⟩

theorem planes_len {G : Fork} : ∀ {js : List ℕ} {vs : List (List E)}, PlanesAt js vs G → ∀ v ∈ vs, v.length = 3
  | [], [], _ => fun _ hv => by cases hv
  | _ :: _, _ :: _, ⟨a, _, c⟩ => fun v hv => by
    rcases List.mem_cons.1 hv with rfl | hv
    · exact a
    · exact planes_len c v hv
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem flatten_one : ∀ (a b : List (List E)), (∀ v ∈ a, v.length = 3) → (∀ v ∈ b, v.length = 3) →
    a.flatten = b.flatten → a = b
  | [], [], _, _, _ => rfl
  | [], v :: b, _, hb, h => by
    have := congrArg List.length h
    simp [hb v (List.mem_cons_self ..)] at this
    omega
  | v :: a, [], ha, _, h => by
    have := congrArg List.length h
    simp [ha v (List.mem_cons_self ..)] at this
  | v :: a, w :: b, ha, hb, h => by
    rw [List.flatten_cons, List.flatten_cons] at h
    have d := List.append_inj h (by rw [ha v (List.mem_cons_self ..), hb w (List.mem_cons_self ..)])
    rw [d.1, flatten_one a b (fun x hx => ha x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx)) d.2]

theorem left_nil {G : Fork} : ∀ {ps : List (ℕ × ℕ)} {os : List (ℕ × MaskedSum.Heard)} {pre : List E}
    {l : List (List E × PscH)}, UnitsAt ps os pre l G → ps ≠ [] → leftOf pre l = []
  | _ :: _, _ :: _, _, (_, _) :: _, _, _ => rfl
  | [], _, _, _, _, h => absurd rfl h
  | _ :: _, [], _, _, h, _ => by cases ‹List (List E × PscH)› <;> simp [UnitsAt] at h
  | _ :: _, _ :: _, _, [], h, _ => by simp [UnitsAt] at h

/-- **The rounds fix the lists.** -/
theorem lists_one {x : Params.AttentionRounds} {h h' : Heard} {G G' : Fork} {L L' : Lists} {rs : List Fmt.RoundView}
    (hne : x.score ≠ []) (hs : Said x h G L) (hs' : Said x h' G' L') (r : RoundsAre L.rounds rs)
    (r' : RoundsAre L'.rounds rs) : L = L' := by
  obtain ⟨u1, u2, rs1, a, a'⟩ := units_one _ _ _ _ _ _ _ rs hs.units hs'.units r r'
  obtain ⟨e1, eE, rs2, b, b'⟩ := sum_one (by rw [sumAt_rs hs.sE, sumAt_rs hs'.sE]) a a'
  rcases rs2 with _ | ⟨q1, rs2⟩
  · exact b.elim
  have exV := (round_one b.1 b'.1).2
  obtain ⟨eC, eM, rs3, c, c'⟩ := sum_one (by rw [sumAt_rs hs.sM, sumAt_rs hs'.sM]) b.2 b'.2
  obtain ⟨_, eVD, rs4, d, d'⟩ := sum_one (by rw [sumAt_rs hs.sVD, sumAt_rs hs'.sVD]) c c'
  rcases rs4 with _ | ⟨q2, _ | ⟨q3, rs4⟩⟩
  · exact d.elim
  · exact d.2.elim
  have ept := (round_one d.1 d'.1).2
  obtain ⟨evM, exF⟩ := round_one d.2.1 d'.2.1
  obtain ⟨_, eF, rs5, f, f'⟩ := sum_one (by rw [sumAt_rs hs.sF, sumAt_rs hs'.sF]) d.2.2 d'.2.2
  rcases rs5 with _ | ⟨q4, rs5⟩
  · exact f.elim
  have exD := (round_one f.1 f'.1).2
  obtain ⟨_, eD, rs6, g, g'⟩ := sum_one (by rw [sumAt_rs hs.sD, sumAt_rs hs'.sD]) f.2 f'.2
  rcases rs6 with _ | ⟨q5, rs6⟩
  · exact g.elim
  have exH := (round_one g.1 g'.1).2
  obtain ⟨_, eH, _⟩ := sum_one (r := []) (r' := []) (H := L.HH) (H' := L'.HH) (t := []) (t' := []) (rs := rs6)
    (by rw [sumAt_rs hs.sH, sumAt_rs hs'.sH])
    (by rw [List.append_nil]; exact g.2) (by rw [List.append_nil]; exact g'.2)
  have ePl : L.planes = L'.planes := flatten_one _ _ (planes_len hs.planes) (planes_len hs'.planes) (u1 hne)
  unfold Lists.ridersE at e1
  rw [left_nil hs.units hne, left_nil hs'.units hne, List.nil_append, List.nil_append] at e1
  have s1 := List.append_inj e1 (by rw [hs.l5, hs'.l5])
  have s2 := List.append_inj s1.2 (by rw [hs.lI, hs'.lI])
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18⟩ := L
  obtain ⟨p1', p2', p3', p4', p5', p6', p7', p8', p9', p10', p11', p12', p13', p14', p15', p16', p17', p18'⟩ := L'
  simp only [List.cons.injEq, and_true] at exV exF exD exH
  simp only at ePl u2 s1 s2 eE eC eM eVD ept evM eF eD eH exV exF exD exH
  obtain ⟨s11, _⟩ := s1
  obtain ⟨s21, s22⟩ := s2
  subst ePl u2 s11 s21 s22 eE exV eC eM eVD ept evM exF eF exD eD exH eH
  rfl

section Data
open Iop Prob Cb TWhole Cb.Pv.Att
open OnBytes.Tie.Pv.Att (UnitsH TailH)

variable {K : Type} [Field K] [Fintype K]

/-! ## The ties fix the data -/

/-- Two data of one sumcheck with the same ties are one. -/
theorem sumH_one {ρ : Reading K} {M Y : Type} {S : SumL K M Y} {D D' : OnBytes.Tie.Pv.Att.SumH ρ S} {riders : List E}
    {H : OnBytes.Tie.Pv.Att.PscH} {hh : VerifiableInference.Desc.Part.MaskedSum.Heard} {a : Add S}
    (o : OfP D riders H hh) (o' : OfP D' riders H hh) (v : ValsOf D a) (v' : ValsOf D' a) : D = D' := by
  obtain ⟨r, H0, b, w, st, t⟩ := D
  obtain ⟨r', H0', b', w', st', t'⟩ := D'
  have e1 : r = r' := o.r.trans o'.r.symm
  have e2 : H0 = H0' := o.H.trans o'.H.symm
  have e3 : t = t' := o.t.trans o'.t.symm
  have e4 : st = st' := v.2.trans v'.2.symm
  subst e1 e2 e3 e4
  have e5 : w = w' := funext fun x => (v.1 x).trans (v'.1 x).symm
  subst e5
  rfl

/-- Two data of the tail with the same ties are one. -/
theorem tailH_one {ρ : Reading K} {M Y : Type} {T : Tail K M Y} {d d' : TailH ρ T} {x : Params.AttentionRounds}
    {h : Heard} {L : Lists} {a : TailAdd T} (o : TailOfP d x h L) (o' : TailOfP d' x h L) (v : TailVals d a)
    (v' : TailVals d' a) : d = d' := by
  obtain ⟨dE, xV, dVM, dVD, pts, mx, xF, dF, xD, dD, xH, dH⟩ := d
  obtain ⟨dE', xV', dVM', dVD', pts', mx', xF', dF', xD', dD', xH', dH'⟩ := d'
  have e1 : dE = dE' := sumH_one o.oE o'.oE v.vE v'.vE
  have e2 : dVM = dVM' := sumH_one o.oM o'.oM v.vM v'.vM
  have e3 : dVD = dVD' := sumH_one o.oVD o'.oVD v.vVD v'.vVD
  have e4 : dF = dF' := sumH_one o.oF o'.oF v.vF v'.vF
  have e5 : dD = dD' := sumH_one o.oD o'.oD v.vD v'.vD
  have e6 : dH = dH' := sumH_one o.oH o'.oH v.vH v'.vH
  have f1 : xV = xV' := o.xV.trans o'.xV.symm
  have f2 : pts = pts' := o.pts.trans o'.pts.symm
  have f3 : mx = mx' := o.mx.trans o'.mx.symm
  have f4 : xF = xF' := o.xF.trans o'.xF.symm
  have f5 : xD = xD' := o.xD.trans o'.xD.symm
  have f6 : xH = xH' := o.xH.trans o'.xH.symm
  subst e1 e2 e3 e4 e5 e6 f1 f2 f3 f4 f5 f6
  rfl

/-- Two data of the units with the same ties are one. -/
theorem unitsH_one {ρ : Reading K} {M Y : Type} : ∀ (us : List (SumL K M (Seen K Y))) (d d' : UnitsH ρ us)
    (ps : List (ℕ × ℕ)) (os : List (ℕ × VerifiableInference.Desc.Part.MaskedSum.Heard)) (pre : List E)
    (l : List (List E × OnBytes.Tie.Pv.Att.PscH)) (a : UnitsAdd us), UnitsOfP us d ps os pre l →
    UnitsOfP us d' ps os pre l → UnitsVals us d a → UnitsVals us d' a → d = d'
  | [], _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _ :: us, d, d', _ :: ps, _ :: os, _, (_, _) :: l, a, ⟨_, o, o2⟩, ⟨_, o', o2'⟩, ⟨v, v2⟩, ⟨v', v2'⟩ =>
    Prod.ext (sumH_one o o' v v') (unitsH_one us d.2 d'.2 ps os [] l a.2 o2 o2' v2 v2')
  | _ :: _, _, _, [], _, _, _, _, h, _, _, _ => h.elim
  | _ :: _, _, _, _ :: _, [], _, _, _, h, _, _, _ => h.elim
  | _ :: _, _, _, _ :: _, _ :: _, _, [], _, h, _, _, _ => h.elim

end Data

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.tailH_one
#print axioms VerifiableInference.Desc.First.Att.P.unitsH_one
#print axioms VerifiableInference.Desc.First.Att.P.lists_one
