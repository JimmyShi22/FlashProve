-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3Via/TiesSum.lean: the kind "lookup" (K3): the hearing on a view's rounds against the
flat text: the masked sumcheck's two pieces. Theorems, over Johnson/Top/H/P1Tie/ (the tie of the two
texts of the masked sumcheck).

Main theorems:
  `cut_standIn`: the flat course (WholeCut) gives the stand-in's yes.
  `call_tape`, `open_tape`: the strict tape of one call's rounds is made, from what the hearing
    itself tests: every item a scalar and the numbers sent and drawn (the part's reading); no
    position and no matrix entry drawn (elementsAlone); Y's draw not 0 (sumV's guard); with
    `staticT` of the call's own entries.
  `ties_sum`: sumV against wholeStandIn.
  `ties_open`: openV against Fl.pscBegin, then Fl.roundsIn .eq.
The entries are written so that they read numbers alone (`sumE`, `openE`): a point's coordinates are
heard, its length is public.

Limits. One way, as `Ties` is (Johnson/Top/H/K3Via/Ties.lean). A tie: it has no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3Via.Ties

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum
  (Var Call Ends Read Heard entry entries callOf openCall pts opts varY ReadsFirst
  varRounds roundOf readAll whole)
open VerifiableInference.Desc.First.Tape (tapeT roundT)
open VerifiableInference.Desc.First.Prod (Whole wholeStandIn)
open VerifiableInference.Desc.K3Cut (WholeCut bindM shownM)
open First.ProdV (elementsAlone)

/-! ## From the flat course to the stand-in's yes -/

theorem shownsM (s : Nat) (F : Fork) (t : Tape) (g : Nat → E) :
    ∀ (l : List Nat), (∀ i ∈ l, F.shown (s + i) = some (g i)) →
    (l.mapM fun i => Fl.shown (s + i)) F t = some (l.map g, F, t)
  | [], _ => by
    rw [List.mapM_nil]
    rfl
  | i :: l, h => by
    rw [List.mapM_cons]
    refine bindM (shownM (h i (by simp)) t) ?_
    refine bindM (shownsM s F t g l (fun j hj => h j (List.mem_cons_of_mem _ hj))) ?_
    rfl

/-- **The flat course gives the stand-in's yes.** -/
theorem cut_standIn {C : Aff} {zs : List E} {dY n : Nat} {e : List E → E} {F G : Fork} {t u : Tape}
    {w : Whole}
    (hread : ReadsFirst n e) (h : WholeCut C zs dY n e F t w G u) :
      wholeStandIn C zs dY n e F t = some (w, G, u) := by
  obtain ⟨p0, F0, t0, p1, F1, t1, p2, F2, t2, ends, p3, k0, k1, k2, k3, k4, k5⟩ := h
  have he : e ((List.range n).map fun i => ends.getD i zeroE) = e ends :=
    hread _ _ (fun i hi => MaskedSum.getD_map_range _ n i hi)
  have k4' : Fl.pscRow p2 (e ((List.range n).map fun i => ends.getD i zeroE)) {} F2 t2 =
    some ((w.row, p3), G, u) := by
    rw [he]
    exact k4
  unfold First.Prod.wholeStandIn
  refine bindM k0 ?_
  refine bindM k1 ?_
  refine bindM k2 ?_
  refine bindM (shownsM w.sEnd F2 t2 (fun i => ends.getD i zeroE) (List.range n)
    (fun i hi => k3 i (List.mem_range.1 hi))) ?_
  refine bindM k4' ?_
  show some (({ challenges := p2.r.toList, sEnd := w.sEnd, row := w.row } : Whole), G, u) =
    some (w, G, u)
  rw [← k5]

/-! ## The entries, by numbers alone -/

/-- The entries of a masked sumcheck with ends: m variables of three coefficients. -/
def sumE (m dY n : Nat) : List Fmt.Entry :=
  entry "PSC epsilon" 1 1 0 ::
    (List.replicate m (entry "PSC round" 2 1 0) ++ [entry "PSC Y" dY 1 1, entry "PSC values" n 0 0])

/-- The entries of a masked sumcheck that is left open: a variable for each degree. -/
def openE (ds : List Nat) : List Fmt.Entry := entry "PSC epsilon" 1 1 0 :: ds.map fun d =>
    entry "PSC round" d 1 0

theorem varsE_pts : ∀ (zs : List E), ((pts zs).map fun v => entry "PSC round" (v.d - 1) 1 0) =
    List.replicate zs.length (entry "PSC round" 2 1 0)
  | [] => rfl
  | _ :: zs => congrArg (entry "PSC round" 2 1 0 :: ·) (varsE_pts zs)

theorem varsE_opts : ∀ (zs : List (E × Nat)),
    ((opts zs).map fun v => entry "PSC round" (v.d - 1) 1 0) =
    (zs.map (·.2)).map fun d => entry "PSC round" d 1 0
  | [] => rfl
  | x :: zs => by
    show entry "PSC round" (x.2 + 1 - 1) 1 0 ::
      ((opts zs).map fun v => entry "PSC round" (v.d - 1) 1 0) =
      entry "PSC round" x.2 1 0 :: ((zs.map (·.2)).map fun d => entry "PSC round" d 1 0)
    rw [varsE_opts zs, Nat.add_sub_cancel]

theorem entries_callOf (zs : List E) (dY n : Nat) :
    entries (callOf zs dY n) = sumE zs.length dY n := by
  show ([entry "PSC epsilon" (0 + 1) 1 0] ++
    ((pts zs).map fun v => entry "PSC round" (v.d - 1) 1 0)) ++
      [entry "PSC Y" dY 1 1, entry "PSC values" n 0 0] = _
  rw [varsE_pts]
  rfl

theorem entries_openCall (zs : List (E × Nat)) : entries (openCall zs) = openE (zs.map (·.2)) := by
  show ([entry "PSC epsilon" (0 + 1) 1 0] ++
    ((opts zs).map fun v => entry "PSC round" (v.d - 1) 1 0)) ++
      ([] : List Fmt.Entry) = _
  rw [varsE_opts, List.append_nil]
  rfl

/-! ## The strict tape of one call's rounds -/

theorem alone_cons {r : Fmt.RoundView} {rs : List Fmt.RoundView} (h : elementsAlone (r :: rs) = true) :
    (r.drawn.poss.isEmpty = true ∧ r.drawn.trits.isEmpty = true) ∧ elementsAlone rs = true := by
  have h' : ((r.drawn.poss.isEmpty && r.drawn.trits.isEmpty) && elementsAlone rs) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h'
  exact h'

theorem static_cons {e : Fmt.Entry} {es : List Fmt.Entry} (h : (e :: es).all staticT = true) :
    staticT e = true ∧ es.all staticT = true := by
  have h' : (staticT e && es.all staticT) = true := h
  rw [Bool.and_eq_true] at h'
  exact h'

/-- The variables' rounds. -/
theorem vars_tape : ∀ (vs : List Var) (rs rest : List Fmt.RoundView) (l : List (List E × E)),
    varRounds vs rs = some (l, rest) →
    elementsAlone rs = true → (vs.map fun v => entry "PSC round" (v.d - 1) 1 0).all staticT = true →
    ∃ used t, rs = used ++ rest ∧ tapeT {} used (vs.map fun v => entry "PSC round" (v.d - 1) 1 0) =
      some t ∧
      elementsAlone rest = true
  | [], rs, rest, l, h, ha, _ => by
    rw [MaskedSum.varRounds_nil] at h
    have e := Option.some.inj h
    cases e
    exact ⟨[], [], rfl, rfl, ha⟩
  | v :: vs, [], rest, l, h, _, _ => by
    have h' : (none : Option (List (List E × E) × List Fmt.RoundView)) = some (l, rest) := h
    cases h'
  | v :: vs, r0 :: rs, rest, l, h, ha, hs => by
    obtain ⟨s, g, l', h1, h2, -⟩ := MaskedSum.varRounds_cons_some h
    obtain ⟨a1, a2, a3, -⟩ := MaskedSum.roundOf_some h1
    obtain ⟨⟨c1, c2⟩, c3⟩ := alone_cons ha
    obtain ⟨s1, s2⟩ := static_cons hs
    obtain ⟨used, t, q1, q2, q3⟩ := vars_tape vs rs rest l' h2 c3 s2
    have hT := roundT_mk (e := entry "PSC round" (v.d - 1) 1 0) s1 a1 a3 c1 c2
      (by show 24 * (v.d - 1) = 24 * s.length; rw [a2]) (nz_none _ 1 a3)
    exact ⟨r0 :: used, _ :: t, by rw [q1]; rfl, tapeT_cons_mk hT q2, q3⟩

/-- The first round. -/
theorem first_round {r0 : Fmt.RoundView} {mu eps : E} (h : roundOf 1 1 r0 = some ([mu], [eps]))
    (c1 : r0.drawn.poss.isEmpty = true) (c2 : r0.drawn.trits.isEmpty = true)
    (s1 : staticT (entry "PSC epsilon" 1 1 0) = true) :
      ∃ x, roundT {} r0 (entry "PSC epsilon" 1 1 0) = some x := by
  obtain ⟨a1, -, a3, -⟩ := MaskedSum.roundOf_some h
  exact ⟨_, roundT_mk (e := entry "PSC epsilon" 1 1 0) s1 a1 a3 c1 c2 rfl (nz_none _ 1 a3)⟩

/-- **The strict tape of a call with ends is made.** -/
theorem call_tape {zs : List E} {dY n : Nat} {rs : List Fmt.RoundView} {x : Read}
    (hR : readAll (callOf zs dY n) rs = some x)
    (ha : elementsAlone rs = true) (hnz : isZeroE ((x.rounds.map (·.2)).getLastD zeroE) = false)
    (hs : (entries (callOf zs dY n)).all staticT = true) :
      ∃ t, tapeT {} rs (entries (callOf zs dY n)) = some t := by
  obtain ⟨mu, eps, rounds, values⟩ := x
  obtain ⟨r0, rest, rv, d, ers, q0, qv, qe⟩ :=
    MaskedSum.readAll_ends_some (vs := pts zs) (e := ⟨dY, n⟩) hR
  subst ers
  obtain ⟨l1, mid, l2, v1, v2, el, -⟩ :=
    MaskedSum.varRounds_append_some (pts zs) [varY dY] rest [rv] rounds qv
  have el' : rounds = l1 ++ l2 := el
  subst el'
  have hs' : (entry "PSC epsilon" 1 1 0 ::
    (((pts zs).map fun v => entry "PSC round" (v.d - 1) 1 0) ++
      [entry "PSC Y" dY 1 1, entry "PSC values" n 0 0])).all staticT = true := hs
  obtain ⟨s0, s1⟩ := static_cons hs'
  rw [List.all_append, Bool.and_eq_true] at s1
  obtain ⟨sV, sE⟩ := s1
  obtain ⟨sY, sE'⟩ := static_cons sE
  obtain ⟨sVal, -⟩ := static_cons sE'
  obtain ⟨⟨c1, c2⟩, c3⟩ := alone_cons ha
  obtain ⟨x0, hx0⟩ := first_round q0 c1 c2 s0
  obtain ⟨used, t, u1, u2, u3⟩ := vars_tape (pts zs) rest mid l1 v1 c3 sV
  cases mid with
  | nil =>
    have h' : (none : Option (List (List E × E) × List Fmt.RoundView)) = some (l2, [rv]) := v2
    cases h'
  | cons rY mid' =>
    obtain ⟨sYs, beta, l', w1, w2, e2⟩ := MaskedSum.varRounds_cons_some v2
    rw [MaskedSum.varRounds_nil] at w2
    have e3 := Option.some.inj w2
    cases e3
    subst e2
    obtain ⟨⟨y1, y2⟩, y3⟩ := alone_cons u3
    obtain ⟨⟨z1, z2⟩, -⟩ := alone_cons y3
    obtain ⟨b1, b2, b3, b4⟩ := MaskedSum.roundOf_some w1
    obtain ⟨d1, d2, d3, -⟩ := MaskedSum.roundOf_some qe
    have hbeta : isZeroE beta = false := by
      have k : ((l1 ++ [(sYs, beta)]).map (·.2)).getLastD zeroE = beta := by simp
      rw [k] at hnz
      exact hnz
    have hnzY : ((rY.drawn.elems.drop (1 - 1)).all fun x => !isZeroE (E.ofTriple x)) = true := by
      have k : (rY.drawn.elems.all fun x => !isZeroE (E.ofTriple x)) =
          ((rY.drawn.elems.map E.ofTriple).all fun y => !isZeroE y) := by
        rw [List.all_map]
        rfl
      show (rY.drawn.elems.all fun x => !isZeroE (E.ofTriple x)) = true
      rw [k, ← b4]
      simp [hbeta]
    have hTY := roundT_mk (e := entry "PSC Y" dY 1 1) sY b1 b3 y1 y2
      (by show 24 * dY = 24 * sYs.length; rw [b2]; rfl) hnzY
    have hTV := roundT_mk (e := entry "PSC values" n 0 0) sVal d1 d3 z1 z2
      (by show 24 * n = 24 * values.length; rw [d2]) (nz_none _ 0 d3)
    have key := tapeT_cons_mk hx0 (tapeT_append _ _ _ _ _ _ u2 (tapeT_cons_mk hTY (tapeT_one hTV)))
    rw [u1]
    exact ⟨_, key⟩

/-- **The strict tape of a call that is left open is made.** -/
theorem open_tape {zs : List (E × Nat)} {rs : List Fmt.RoundView} {x : Read}
    (hR : readAll (openCall zs) rs = some x)
    (ha : elementsAlone rs = true) (hs : (entries (openCall zs)).all staticT = true) :
    ∃ t, tapeT {} rs (entries (openCall zs)) = some t := by
  obtain ⟨r0, rest, ers, q0, qv, -⟩ := MaskedSum.readAll_open_some (vs := opts zs) hR
  subst ers
  have hs' : (entry "PSC epsilon" 1 1 0 ::
    (((opts zs).map fun v => entry "PSC round" (v.d - 1) 1 0) ++
      ([] : List Fmt.Entry))).all staticT = true := hs
  rw [List.append_nil] at hs'
  obtain ⟨s0, sV⟩ := static_cons hs'
  obtain ⟨⟨c1, c2⟩, c3⟩ := alone_cons ha
  obtain ⟨x0, hx0⟩ := first_round q0 c1 c2 s0
  obtain ⟨used, t, u1, u2, -⟩ := vars_tape (opts zs) rest [] x.rounds qv c3 sV
  rw [List.append_nil] at u1
  subst u1
  have he : entries (openCall zs) = entry "PSC epsilon" 1 1 0 ::
    ((opts zs).map fun v => entry "PSC round" (v.d - 1) 1 0) := by
    show ([entry "PSC epsilon" (0 + 1) 1 0] ++
      ((opts zs).map fun v => entry "PSC round" (v.d - 1) 1 0)) ++
      ([] : List Fmt.Entry) = _
    rw [List.append_nil]
    rfl
  rw [he]
  exact ⟨_, tapeT_cons_mk hx0 u2⟩

/-! ## sumV -/

theorem sum_some {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs rest : List Fmt.RoundView}
    {a : Heard × Aff} (h : sumV C k endTerm F rs = some (a, G, rest)) :
    elementsAlone (rs.take (roundsOf k)) = true ∧ whole C k endTerm F (rs.take (roundsOf k)) =
      some (a.1, a.2, G) ∧
      isZeroE (a.1.r.getLastD zeroE) = false ∧ rest = rs.drop (roundsOf k) := by
  unfold sumV at h
  cases ha : elementsAlone (rs.take (roundsOf k)) with
  | false =>
    rw [ha] at h
    have h' : (none : Option ((Heard × Aff) × Fork × List Fmt.RoundView)) = some (a, G, rest) := h
    cases h'
  | true =>
    rw [ha] at h
    cases hw : whole C k endTerm F (rs.take (roundsOf k)) with
    | none =>
      rw [hw] at h
      have h' : (none : Option ((Heard × Aff) × Fork × List Fmt.RoundView)) = some (a, G, rest) := h
      cases h'
    | some y =>
      obtain ⟨h0, row0, G0⟩ := y
      rw [hw] at h
      cases hz : isZeroE (h0.r.getLastD zeroE) with
      | true =>
        have h1 : (if isZeroE (h0.r.getLastD zeroE) then none else some
          ((h0, row0), G0, rs.drop (roundsOf k))) =
            some (a, G, rest) := h
        rw [hz] at h1
        have h' : (none : Option ((Heard × Aff) × Fork × List Fmt.RoundView)) = some (a, G, rest) := h1
        cases h'
      | false =>
        have h1 : (if isZeroE (h0.r.getLastD zeroE) then none else some
          ((h0, row0), G0, rs.drop (roundsOf k))) =
            some (a, G, rest) := h
        rw [hz] at h1
        have h' : some ((h0, row0), G0, rs.drop (roundsOf k)) = some (a, G, rest) := h1
        cases h'
        exact ⟨rfl, rfl, hz, rfl⟩

/-- **A masked sumcheck with ends.** m: the number of its variables. -/
theorem ties_sum (C : Aff) (zs : List E) (m dY n : Nat) (e : List E → E) (hm : zs.length = m)
    (hread : ReadsFirst n e) :
    Ties (fun (a : Heard × Aff) (w : Whole) => w = ⟨a.1.r, a.1.sEnd, a.2⟩) (sumE m dY n)
      (sumV C (callOf zs dY n) fun _ sh => e sh) (wholeStandIn C zs dY n e) := by
  intro hs F G rs rest a h
  rw [← hm, ← entries_callOf] at hs
  obtain ⟨ha, hw, hz, rfl⟩ := sum_some h
  obtain ⟨e0, G0, sh, -, hh, -, -⟩ := MaskedSum.whole_some hw
  obtain ⟨-, T, x, -, hR, -, hrec⟩ := MaskedSum.hear_some hh
  have hz' : isZeroE ((x.rounds.map (·.2)).getLastD zeroE) = false := by
    rw [hrec] at hz
    exact hz
  obtain ⟨t, ht⟩ := call_tape hR ha hz' hs
  obtain ⟨i1, i2⟩ := MaskedSum.tape_is {} _ _ t ht
  refine ⟨rs.take (roundsOf (callOf zs dY n)), t, _, (List.take_append_drop _ _).symm, ?_, rfl,
    fun u => ?_⟩
  · rw [← hm, ← entries_callOf]
    exact ht
  · exact cut_standIn hread (MaskedSum.whole_cut C zs dY n e F G _ a.1 a.2 t u hw i1 i2)

/-! ## openV -/

theorem open_some {C : Aff} {vs : List Var} {F G : Fork} {rs rest : List Fmt.RoundView} {a : Heard}
    (h : openV C vs F rs = some (a, G, rest)) :
    elementsAlone (rs.take (vs.length + 1)) = true ∧
      MaskedSum.hear C { lead := 0, vs := vs, ends := none } F (rs.take (vs.length + 1)) =
        some (a, G) ∧
      rest = rs.drop (vs.length + 1) := by
  unfold openV at h
  cases ha : elementsAlone (rs.take (vs.length + 1)) with
  | false =>
    rw [ha] at h
    have h' : (none : Option (Heard × Fork × List Fmt.RoundView)) = some (a, G, rest) := h
    cases h'
  | true =>
    rw [ha] at h
    cases hw : MaskedSum.hear C { lead := 0, vs := vs, ends := none } F
      (rs.take (vs.length + 1)) with
    | none =>
      rw [hw] at h
      have h' : (none : Option (Heard × Fork × List Fmt.RoundView)) = some (a, G, rest) := h
      cases h'
    | some y =>
      rw [hw] at h
      have h' : some (y.1, y.2, rs.drop (vs.length + 1)) = some (a, G, rest) := h
      cases h'
      exact ⟨rfl, rfl, rfl⟩

/-- **A masked sumcheck that is left open.** ds: its variables' degrees. -/
theorem ties_open (C : Aff) (zs : List (E × Nat)) (ds : List Nat) (hd : zs.map (·.2) = ds) :
    Ties (fun (a : Heard) (b : Array E × Psc) => b = (a.r.toArray, a.psc false)) (openE ds)
      (openV C (opts zs)) (Fl.pscBegin C >>= fun p => Fl.roundsIn .eq p zs) := by
  intro hs F G rs rest a h
  rw [← hd, ← entries_openCall] at hs
  obtain ⟨ha, hh, rfl⟩ := open_some h
  have hh' : MaskedSum.hear C (openCall zs) F (rs.take ((opts zs).length + 1)) = some (a, G) := hh
  obtain ⟨-, T, x, -, hR, -, -⟩ := MaskedSum.hear_some hh'
  obtain ⟨t, ht⟩ := open_tape hR ha hs
  obtain ⟨i1, i2⟩ := MaskedSum.tape_is {} _ _ t ht
  refine ⟨rs.take ((opts zs).length + 1), t, _, (List.take_append_drop _ _).symm, ?_, rfl, fun u =>
    ?_⟩
  · rw [← hd, ← entries_openCall]
    exact ht
  · obtain ⟨p0, F0, t0, k0, k1⟩ := MaskedSum.hear_open C zs F G _ a t u hh' i1 i2
    exact bindM k0 k1

end VerifiableInference.Desc.K3
