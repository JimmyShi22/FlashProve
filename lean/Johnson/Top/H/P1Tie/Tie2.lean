-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/P1Tie/Tie2.lean: the tie of the two texts of the masked sumcheck, second half: from
the flat course to the part's yes. Theorems.

Main theorems:
  `course_facts`: where the flat steps return, the tape began with just the call's rounds, under the
    call's names.
  `cut_took : Spec.cut_took`: how much of the tape the course takes.
  `cut_whole : Spec.cut_whole`.

How it goes. Johnson/Top/H/FlPort/PscRun.lean says what a flat step that returns has read; here the
names are kept too. So the tape's shape is known; with `IsTape` the part reads the view's rounds;
its hearing returns; and by the first half (Johnson/Top/H/P1Tie/Tie1.lean) the flat functions return
on that same tape what the part has heard: a function has one value: so the two courses are one. No
arithmetic is done twice. As machine words; no premise on words.

Limits. Those of Johnson/Top/H/P1Tie/Stmt.lean's head. A tie: it has no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.P1Tie.Tie1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Aff Fork Psc RoundForm)
open VerifiableInference.Desc.First.Prod (Whole)
open VerifiableInference.Desc.K3Cut (WholeCut bindS pureS stepW stepW_ok)

/-! ## A close that returns: the name and the number were the call's -/

theorem closeOne_inv {name : String} {nz : Nat} {c c' : Tape} {x : E}
    (h : closeOne name nz c = some (x, c')) :
    ∃ w, c = ⟨some name, nz, w, [], [x]⟩ :: c' := by
  obtain ⟨nm, z, w, rfl⟩ := Fo.Tp.closeOne_some h
  have h' : (if nm == name && z == nz then some (x, c') else none) = some (x, c') := h
  split at h'
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨w, rfl⟩
  · cases h'

theorem emptyOn_inv {name : String} {c c' : Tape} (h : Fl.emptyOn name c = some ((), c')) :
    ∃ w, c = ⟨some name, 0, w, [], []⟩ :: c' := by
  obtain ⟨nm, z, w, rfl⟩ := Fo.Tp.emptyOn_some h
  cases hc : (nm == name && z == 0 && ([] : List E).length == 0) with
  | false =>
    have h' :
      ((if nm == name && z == 0 && ([] : List E).length == 0 then some (([] : List E), c') else
        none).map
        fun x => ((), x.2)) = some ((), c') := h
    rw [hc] at h'
    simp at h'
  | true =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hc
    exact ⟨w, rfl⟩

/-! ## The flat steps that return -/

theorem begin_inv {C : Aff} {F F0 : Fork} {c t0 : Tape} {p0 : Psc}
    (h : Fl.pscBegin C F c = some (p0, F0, t0)) :
    ∃ T mu eps w, F.publicPart C = some T ∧ c = ⟨some "PSC epsilon", 0, w, [mu], [eps]⟩ :: t0 ∧ F0 =
      tk F 1 := by
  obtain ⟨T, mu, eps, hT, hev, hF, -⟩ := Fo.Tp.pscBegin_ok C F F0 c t0 p0 h
  obtain ⟨c1, h1, c2, h2, e⟩ := hev
  have e' : t0 = c2 := e
  subst e'
  have h1' : recv c = some (mu, c1) := h1
  have h2' : closeOne Model.RoundName.pscEpsilon.name 0 c1 = some (eps, t0) := h2
  obtain ⟨w, rfl⟩ := closeOne_inv h2'
  obtain ⟨nm, z, w', s, d, t, e1, e2⟩ := Fo.Tp.recv_some h1'
  cases e2
  exact ⟨T, mu, eps, w, hT, e1, hF⟩

theorem step_inv {p p' : Psc} {z : E} {F F' : Fork} {c c' : Tape}
    (h : stepW p z F c = some (p', F', c')) :
    ∃ w sent x, c = ⟨some "PSC round", 0, w, sent, [x]⟩ :: c' ∧ sent.length = 2 ∧ F' = tk F 2 := by
  obtain ⟨x, hx, -⟩ := stepW_ok h
  obtain ⟨wt, sent, -, hw, -, -, hev, hF, -⟩ := Fo.Tp.roundIn_ok .eq2 p z 0 F F' c c' x p' hx
  have hw' : some (OnBytes.Psc.Weight.equality z 3) = some wt := (weight_eq2 z).symm.trans hw
  cases hw'
  obtain ⟨c1, h1, c2, h2, e⟩ := hev
  have e' : c' = c2 := e
  subst e'
  have h1' : recvN (3 - 1) c = some (sent, c1) := h1
  have h2' : closeOne Model.RoundName.pscRound.name 0 c1 = some (x, c') := h2
  obtain ⟨w, rfl⟩ := closeOne_inv h2'
  obtain ⟨g1, g2⟩ := Fo.Tp.recvN_some h1' rfl
  refine ⟨w, sent.toList, x, g2, ?_, hF⟩
  rw [Array.length_toList]
  exact g1

theorem fold_inv : ∀ (zs : List E) (p : Psc) (F : Fork) (c : Tape) (p1 : Psc) (F1 : Fork)
    (c1 : Tape),
    zs.foldlM stepW p F c = some (p1, F1, c1) →
    ∃ tv : Tape, c = tv ++ c1 ∧ tv.length = zs.length ∧
      tv.map keyOf = (zs.map fun _ => ((some "PSC round", 0) : Option String × Nat)) ∧
      (∀ y ∈ tv, y.sent.length = 2 ∧ y.drawn.length = 1) ∧ F1 = tk F (2 * zs.length)
  | [], p, F, c, p1, F1, c1, h => by
    rw [List.foldlM_nil] at h
    obtain ⟨-, e2, e3⟩ := pureS h
    subst e2 e3
    exact ⟨[], rfl, rfl, rfl, fun y hy => by simp at hy, rfl⟩
  | z :: zs, p, F, c, p1, F1, c1, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨q, F2, c2, h1, h2⟩ := bindS h
    obtain ⟨w, sent, x, e1, e2, e3⟩ := step_inv h1
    obtain ⟨tv, g1, g2, g3, g4, g5⟩ := fold_inv zs q F2 c2 p1 F1 c1 h2
    refine ⟨⟨some "PSC round", 0, w, sent, [x]⟩ :: tv, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e1, g1]
      rfl
    · simp [g2]
    · rw [List.map_cons, List.map_cons, g3]
      rfl
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨e2, rfl⟩
      · exact g4 y hy
    · rw [g5, e3, tk_tk]
      have e : 2 + 2 * zs.length = 2 * (z :: zs).length := by
        simp only [List.length_cons]
        omega
      rw [e]

theorem ends_inv {p p' : Psc} {dY n e : Nat} {F G : Fork} {c c' : Tape}
    (h : Fl.pscEnds p dY n F c = some ((e, p'), G, c')) :
    ∃ wY wV sentY beta vals,
      c = ⟨some "PSC Y", 1, wY, sentY, [beta]⟩ :: ⟨some "PSC values", 0, wV, vals, []⟩ :: c' ∧
        sentY.length = dY ∧
      vals.length = n ∧ 1 ≤ dY ∧ 1 ≤ n ∧ (tk F (dY + n)).hideRun (F.next + dY) vals.toArray beta =
        some G := by
  obtain ⟨sent, beta, v, -, b1, b2, s1, s2, hev, he, hG, -⟩ :=
    Fo.Tp.pscEnds_ok p dY n F G c c' e p' h
  obtain ⟨c1, h1, c2, h2, c3, h3, c4, h4, e4⟩ := hev
  have e' : c' = c4 := e4
  subst e'
  have h1' : recvN dY c = some (sent, c1) := h1
  have h2' : closeOne Model.RoundName.pscY.name 1 c1 = some (beta, c2) := h2
  have h3' : recvN n c2 = some (v, c3) := h3
  have h4' : Fl.emptyOn Model.RoundName.pscValues.name c3 = some ((), c') := h4
  obtain ⟨wV, rfl⟩ := emptyOn_inv h4'
  obtain ⟨-, g2⟩ := Fo.Tp.recvN_some h3' rfl
  subst g2
  obtain ⟨wY, rfl⟩ := closeOne_inv h2'
  obtain ⟨-, g4⟩ := Fo.Tp.recvN_some h1' rfl
  subst he
  refine ⟨wY, wV, sent.toList, beta, v.toList, g4, ?_, ?_, b1, b2, ?_⟩
  · rw [Array.length_toList]
    exact s1
  · rw [Array.length_toList]
    exact s2
  · exact hG

/-! ## The tape's shape -/

/-- **What the flat beginning, rounds and ends say where they return, one after the other.** -/
theorem course_facts {C : Aff} {zs : List E} {dY n e : Nat} {F F0 F1 F2 : Fork} {T t0 t1 t2 : Tape}
    {p0 p1 p2 : Psc}
    (k0 : Fl.pscBegin C F T = some (p0, F0, t0)) (k1 : zs.foldlM stepW p0 F0 t0 = some (p1, F1, t1))
    (k2 : Fl.pscEnds p1 dY n F1 t1 = some ((e, p2), F2, t2)) :
    ∃ (Tt mu eps : E) (w0 : Nat) (tv : Tape) (wY wV : Nat) (sentY : List E) (beta : E)
      (vals : List E),
      F.publicPart C = some Tt ∧
      T = ⟨some "PSC epsilon", 0, w0, [mu], [eps]⟩ ::
        (tv ++ (⟨some "PSC Y", 1, wY, sentY, [beta]⟩ :: ⟨some "PSC values", 0, wV, vals, []⟩ ::
          t2)) ∧
      tv.length = zs.length ∧ tv.map keyOf =
        (zs.map fun _ => ((some "PSC round", 0) : Option String × Nat)) ∧
      (∀ y ∈ tv, y.sent.length = 2 ∧ y.drawn.length = 1) ∧ sentY.length = dY ∧ vals.length = n ∧ 1 ≤
        dY ∧ 1 ≤ n ∧
      (tk (tk (tk F 1) (2 * zs.length)) (dY + n)).hideRun (F.next + 1 + 2 * zs.length + dY)
        vals.toArray beta =
        some F2 := by
  obtain ⟨Tt, mu, eps, w0, hT, a1, f0⟩ := begin_inv k0
  obtain ⟨tv, b1, b2, b3, b4, f1⟩ := fold_inv zs p0 F0 t0 p1 F1 t1 k1
  obtain ⟨wY, wV, sentY, beta, vals, c1, c2, c3, c4, c5, hG⟩ := ends_inv k2
  subst f0 f1
  refine ⟨Tt, mu, eps, w0, tv, wY, wV, sentY, beta, vals, hT, ?_, b2, b3, b4, c2, c3, c4, c5, hG⟩
  rw [a1, b1, c1]

theorem named_shape (zs : List E) (dY n w0 wY wV : Nat) (mu eps beta : E) (tv : Tape)
    (sentY vals : List E)
    (b3 : tv.map keyOf = (zs.map fun _ => ((some "PSC round", 0) : Option String × Nat))) :
    Named (callOf zs dY n) (⟨some "PSC epsilon", 0, w0, [mu], [eps]⟩ ::
      (tv ++ [⟨some "PSC Y", 1, wY, sentY, [beta]⟩, ⟨some "PSC values", 0, wV, vals, []⟩])) := by
  show (_ :: (tv ++ [_, _])).map keyOf = _
  rw [keys_callOf, List.map_cons, List.map_append, b3]
  rfl

theorem cut_took : Spec.cut_took := by
  intro C zs dY n e F G T w u h
  obtain ⟨p0, F0, t0, p1, F1, t1, p2, F2, t2, ends, p3, k0, k1, k2, -, k4, -⟩ := h
  obtain ⟨Tt, mu, eps, w0, tv, wY, wV, sentY, beta, vals, -, s0, s1, -⟩ := course_facts k0 k1 k2
  obtain ⟨-, -, -, -, d1, -, -, -⟩ := Fo.Tp.pscRow_ok p2 (e ends) {} F2 G t2 u w.row p3 k4
  subst d1
  refine ⟨⟨some "PSC epsilon", 0, w0, [mu], [eps]⟩ ::
    (tv ++ [⟨some "PSC Y", 1, wY, sentY, [beta]⟩, ⟨some "PSC values", 0, wV, vals, []⟩]), ?_, ?_⟩
  · rw [s0]
    simp
  · simp [s1]

/-! ## The part reads such a tape's rounds -/

theorem roundOf_tape {r : Fmt.RoundView} {x : FlatRound} {n k : Nat} (hx : IsRound r x)
    (h1 : x.sent.length = n)
    (h2 : x.drawn.length = k) : roundOf n k r = some (x.sent, x.drawn) := by
  have h3 : r.drawn.elems.length = k := by
    rw [hx.2, List.length_map] at h2
    exact h2
  rw [roundOf_mk hx.1 h1 h3, hx.2]

theorem vars_read : ∀ (zs : List E) (tv : Tape) (rs : List Fmt.RoundView) (tr : Tape),
    IsTape rs (tv ++ tr) →
    tv.length = zs.length → (∀ y ∈ tv, y.sent.length = 2 ∧ y.drawn.length = 1) →
    ∃ l rest, varRounds (pts zs) rs = some (l, rest) ∧ IsTape rest tr
  | [], [], rs, tr, ht, _, _ => ⟨[], rs, varRounds_nil rs, ht⟩
  | z :: zs, y :: tv, [], tr, ht, _, _ => by
    have ht' : False := ht
    exact ht'.elim
  | z :: zs, y :: tv, r0 :: rs, tr, ht, hl, hy => by
    have ht' : IsRound r0 y ∧ IsTape rs (tv ++ tr) := ht
    obtain ⟨l, rest, h1, h2⟩ := vars_read zs tv rs tr ht'.2 (Nat.succ.inj hl)
      (fun y' h' => hy y' (List.mem_cons_of_mem _ h'))
    obtain ⟨s1, s2⟩ := hy y (by simp)
    obtain ⟨g, eg⟩ := one_of_length y.drawn s2
    have hr : roundOf ((Var.point z 3).d - 1) 1 r0 = some (y.sent, [g]) := by
      rw [← eg]
      exact roundOf_tape ht'.1 s1 s2
    exact ⟨(y.sent, g) :: l, rest, varRounds_cons_mk (v := Var.point z 3) (vs := pts zs) hr h1, h2⟩
  | [], _ :: _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _ => by simp at hl

theorem readAll_ends_mk {vs : List Var} {e : Ends} {r0 rv : Fmt.RoundView} {rest : List Fmt.RoundView}
    {mu eps : E}
    {l : List (List E × E)} {s d : List E} (h1 : roundOf 1 1 r0 = some ([mu], [eps]))
    (h2 : varRounds (vs ++ [varY e.dY]) rest = some (l, [rv]))
      (h3 : roundOf e.n 0 rv = some (s, d)) :
    readAll ⟨0, vs, some e⟩ (r0 :: rest) = some ⟨mu, eps, l, s⟩ := by
  have hf : firstRound ⟨0, vs, some e⟩ r0 = some ([], [mu], [eps]) := by
    have h1' : roundOf (0 + 1) 1 r0 = some ([mu], [eps]) := h1
    simp only [firstRound, h1', Option.map_some]
    rfl
  have hall : varRounds (Call.all ⟨0, vs, some e⟩) rest = some (l, [rv]) := h2
  simp only [readAll, hf, hall, h3, Option.map_some]

theorem shapeOk_callOf (zs : List E) {dY n : Nat} (h1 : 1 ≤ dY) (h2 : 1 ≤ n) :
    shapeOk (callOf zs dY n) = true := by
  show ((pts zs).all (fun v => decide (2 ≤ v.d) && decide (v.d ≤ 65)) &&
    (decide (1 ≤ dY) && decide (1 ≤ n))) = true
  have h : (pts zs).all (fun v => decide (2 ≤ v.d) && decide (v.d ≤ 65)) = true := by
    rw [List.all_eq_true]
    intro v hv
    obtain ⟨z, _, rfl⟩ := List.mem_map.1 hv
    rfl
  rw [h]
  simp [h1, h2]

/-! ## (2) -/

theorem getD_map_range (g : Nat → E) (n i : Nat) (hi : i < n) :
    ((List.range n).map g).getD i zeroE = g i := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- **(2) The flat course gives the part's yes.** -/
theorem cut_whole : Spec.cut_whole := by
  intro C zs dY n e F G rs w t u hread ht hc
  obtain ⟨wc, ws, wr⟩ := w
  obtain ⟨p0, F0, t0, p1, F1, t1, p2, F2, t2, ends, p3, k0, k1, k2, k3, k4, k5⟩ := hc
  obtain ⟨Tt, mu, eps, w0, tv, wY, wV, sentY, beta, vals, hT, s0, s1, s2, s3, s4, s5, b1, b2, hG⟩ :=
    course_facts k0 k1 k2
  obtain ⟨-, -, -, -, d1, hrow, hwr, -⟩ := Fo.Tp.pscRow_ok p2 (e ends) {} F2 G t2 u wr p3 k4
  subst d1
  have et : t = ⟨some "PSC epsilon", 0, w0, [mu], [eps]⟩ ::
      (tv ++ [⟨some "PSC Y", 1, wY, sentY, [beta]⟩, ⟨some "PSC values", 0, wV, vals, []⟩]) := by
    apply List.append_cancel_right (bs := u)
    rw [s0]
    simp
  subst et
  have hN := named_shape zs dY n w0 wY wV mu eps beta tv sentY vals s2
  -- the part reads the rounds
  cases rs with
  | nil => exact ht.elim
  | cons r0 rest =>
    have ht' : IsRound r0 ⟨some "PSC epsilon", 0, w0, [mu], [eps]⟩ ∧
        IsTape rest
          (tv ++ [⟨some "PSC Y", 1, wY, sentY, [beta]⟩, ⟨some "PSC values", 0, wV, vals, []⟩]) := ht
    have q0 : roundOf 1 1 r0 = some ([mu], [eps]) := roundOf_tape ht'.1 rfl rfl
    obtain ⟨l1, mid, v1, hm⟩ := vars_read zs tv rest _ ht'.2 s1 s3
    match mid, v1, hm with
    | [], _, hm => exact hm.elim
    | [_], _, hm => exact hm.2.elim
    | _ :: _ :: _ :: _, _, hm => exact hm.2.2.elim
    | [rY, rv], v1, hm =>
      have qY : roundOf ((varY dY).d - 1) 1 rY = some (sentY, [beta]) :=
        roundOf_tape hm.1 (by show sentY.length = dY + 1 - 1; omega) rfl
      have qV : roundOf n 0 rv = some (vals, []) := roundOf_tape hm.2.1 s5 rfl
      have v2 : varRounds [varY dY] [rY, rv] = some ([(sentY, beta)], [rv]) :=
        varRounds_cons_mk (v := varY dY) (vs := []) qY (varRounds_nil [rv])
      have hR : readAll (callOf zs dY n) (r0 :: rest) =
        some ⟨mu, eps, l1 ++ [(sentY, beta)], vals⟩ :=
        readAll_ends_mk (vs := pts zs) (e := ⟨dY, n⟩) q0 (varRounds_append_mk _ _ _ _ _ _ _ v1 v2)
          qV
      -- the ledger behind the hearing
      have o1 : ownSlots (callOf zs dY n).all = 1 + 2 * zs.length + dY := slots_pts dY zs 1
      have o3 : ((l1 ++ [(sentY, beta)]).map (·.2)).getLastD zeroE = beta := by simp
      have hL : ledgerOf (callOf zs dY n) F ⟨mu, eps, l1 ++ [(sentY, beta)], vals⟩ = some F2 := by
        show ({ F with next := F.next + ownSlots (callOf zs dY n).all + vals.length } :
          Fork).hideRun
          (F.next + ownSlots (callOf zs dY n).all) vals.toArray
          (((l1 ++ [(sentY, beta)]).map (·.2)).getLastD zeroE) = some F2
        have a5 : F.next + (1 + 2 * zs.length + dY) + n = F.next + 1 + 2 * zs.length + (dY + n) :=
          by omega
        have a6 : F.next + (1 + 2 * zs.length + dY) = F.next + 1 + 2 * zs.length + dY := by omega
        rw [o1, o3, s5, a5, a6]
        exact hG
      have hh := hear_mk (shapeOk_callOf zs b1 b2) hT hR hL
      -- by the first half the flat functions return, on this very tape, what the part has heard
      obtain ⟨p0', F0', t0', p1', F1', t1', k0', k1', k2', hp, hne, hl⟩ := heard_cut hh ht hN u
      have e0 := Option.some.inj (k0.symm.trans k0')
      cases e0
      have e1 := Option.some.inj (k1.symm.trans k1')
      cases e1
      have e2 := Option.some.inj (k2.symm.trans k2')
      have e3 : ws = (P1Tie.heardOf C (callOf zs dY n) F Tt
        ⟨mu, eps, l1 ++ [(sentY, beta)], vals⟩).sEnd :=
        congrArg (fun x => x.1.1) e2
      have e4 : p2 = (P1Tie.heardOf C (callOf zs dY n) F Tt
        ⟨mu, eps, l1 ++ [(sentY, beta)], vals⟩).psc true :=
        congrArg (fun x => x.1.2) e2
      subst e3 e4
      -- the row
      have r2 := hrow
      rw [walk_eq _ true hp] at r2
      have hs : shownEnds (P1Tie.heardOf C (callOf zs dY n) F Tt
        ⟨mu, eps, l1 ++ [(sentY, beta)], vals⟩) n F2 =
          some ((List.range n).map fun i => ends.getD i zeroE) :=
        mapM_mk _ _ _ (fun i hi => k3 i (List.mem_range.1 hi))
      have he : e ((List.range n).map fun i => ends.getD i zeroE) = e ends :=
        hread _ _ (fun i hi => getD_map_range _ n i hi)
      have hw2 : wr = rowAff (P1Tie.heardOf C (callOf zs dY n) F Tt
        ⟨mu, eps, l1 ++ [(sentY, beta)], vals⟩)
          (e ((List.range n).map fun i => ends.getD i zeroE)) {} := by
        rw [hwr, rowForm_eq _ true hp, he]
      subst hw2
      exact ⟨_, whole_mk (e := ⟨dY, n⟩) rfl hh hs (row_mk r2), k5.symm, rfl⟩

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.cut_took
#print axioms VerifiableInference.Desc.Part.MaskedSum.cut_whole
