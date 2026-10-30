-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Cut/CutTie.lean: the lookup's tie of the two sides' roots (`K3.tie`,
Johnson/Desc/First/Look/K3Lookup.lean) gives the library's flat tie (`lkTieStep`, `lkTie`,
OnBytes/K/Kc/FlatHear.lean); and the stand-in for the bits' sumcheck gives the five lines of
`lkPad` that hear it. Theorems with their proofs, each from the part's yes, with the value, the
ledger behind and the tape left spelled out.

Main names:

  `cut_tieStep0`, `cut_tieStep`: the course of a masked sumcheck without a variable (`WholeCut`,
    Johnson/Top/H/Cut/CutWhole.lean) gives step 0, step j > 0. Step 0 of the flat text reads its
    three shown values in another order: reading changes nothing.
  `tieTurn`: one turn of the fold in `K3.tie`, under a name.
  `tie_fold`: `K3.tie`'s yes gives the fold of `lkTieStep` over List.range 31 from {}.
  `tie_lkTie`: with the draw of the five coordinates behind it: `lkTie`.
  `cut_bits`, `whole_bits`: the bits' course, and so the stand-in's yes, gives pscBegin, roundsIn
    .eq2, pscEnds 2 1, shown, pscRow; the array that roundsIn hands back is the first m of the
    challenges.

Limits. One way alone: the flat pieces' yes is not shown to give `K3.tie`'s or the stand-in's. The
number of steps, 31, is that of both texts and is no letter here. `cut_bits` asks that m is the
number of coordinates: the caller pays. These are ties between texts, equations on what they
return: they have no error term. No routine in a context of the verifier program's channel is
named.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Cut.CutWhole
import Johnson.Desc.First.Look.K3Lookup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3Cut
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundForm eqTab)
open OnBytes.Model.Forest (Tie TieStep)
open First.Prod (wholeStandIn Whole)

/-- Step 0 of the tie, from the course of its masked sumcheck. -/
theorem cut_tieStep0 {a : E} {s : TieStep} {F G : Fork} {t u : Tape} {w : Whole}
    (h : WholeCut (Aff.ofConst zeroE) [] 3 3
      (fun v => subE (v.getD 0 zeroE)
        (mulE a (mulE (mulE (v.getD 1 zeroE) (v.getD 1 zeroE)) (v.getD 2 zeroE)))) F t w G u) :
    lkTieStep a s 0 F t =
      some ({ rows := s.rows.push w.row, sZ := w.sEnd, sP := w.sEnd + 1,
              sG := s.sG.push (w.sEnd + 1 + 1) }, G, u) := by
  obtain ⟨p0, F0, t0, p1, F1, t1, p2, F2, t2, ends, p3, h0, h1, h2, hs, h4, -⟩ := h
  rw [List.foldlM_nil] at h1
  obtain ⟨e1, e2, e3⟩ := pureS h1
  subst e1 e2 e3
  unfold lkTieStep
  simp only []
  refine bindM h0 ?_
  refine bindM h2 ?_
  refine bindM (shownM (hs 1 (by omega)) _) ?_
  refine bindM (shownM (hs 2 (by omega)) _) ?_
  refine bindM (shownM (hs 0 (by omega)) _) ?_
  refine bindM (pureM _ _ _) ?_
  refine bindM h4 ?_
  rfl

/-- Step j of the tie, j > 0, from the course of its masked sumcheck. -/
theorem cut_tieStep {a : E} {s : TieStep} {j : Nat} (hj : j ≠ 0) {F G : Fork} {t u : Tape}
    {w : Whole}
    (h : WholeCut (Aff.slot s.sP) [] 3 2
      (fun v => mulE (mulE (v.getD 0 zeroE) (v.getD 0 zeroE)) (v.getD 1 zeroE)) F t w G u) :
    lkTieStep a s j F t =
      some ({ rows := s.rows.push w.row, sZ := s.sZ, sP := w.sEnd,
              sG := s.sG.push (w.sEnd + 1) }, G, u) := by
  obtain ⟨p0, F0, t0, p1, F1, t1, p2, F2, t2, ends, p3, h0, h1, h2, hs, h4, -⟩ := h
  rw [List.foldlM_nil] at h1
  obtain ⟨e1, e2, e3⟩ := pureS h1
  subst e1 e2 e3
  unfold lkTieStep
  simp only [if_neg hj]
  refine bindM h0 ?_
  refine bindM h2 ?_
  refine bindM (shownM (hs 0 (by omega)) _) ?_
  refine bindM (shownM (hs 1 (by omega)) _) ?_
  refine bindM (pureM _ _ _) ?_
  refine bindM h4 ?_
  rfl

/-- One turn of the fold in `K3.tie`: the claims, the slot of the last power, the slots of the
planes' roots. -/
def tieTurn (s : Array Aff × Nat × Array Nat) (_ : Nat) : Fl (Array Aff × Nat × Array Nat) := do
  let w ← wholeStandIn (Aff.slot s.2.1) [] 3 2
    fun v => mulE (mulE (v.getD 0 zeroE) (v.getD 0 zeroE)) (v.getD 1 zeroE)
  pure (s.1.push w.row, w.sEnd, s.2.2.push (w.sEnd + 1))

theorem range31 : List.range 31 = 0 :: List.range' 1 30 := rfl

/-- **The tie's 31 sumchecks.** -/
theorem tie_fold {a : E} {F G : Fork} {t u : Tape} {x : Array Aff × Nat × Array Nat}
    (h : K3.tie a F t = some (x, G, u)) :
    ∃ s : TieStep, (List.range 31).foldlM (lkTieStep a) {} F t = some (s, G, u) ∧
      x = (s.rows, s.sZ, s.sG.push s.sP) := by
  unfold K3.tie at h
  obtain ⟨w, F1, t1, hw, h⟩ := bindS h
  obtain ⟨s, F2, t2, hf, h⟩ := bindS h
  obtain ⟨e1, e2, e3⟩ := pureS h
  subst e1 e2 e3
  have h0 := cut_tieStep0 (s := {}) (whole_ok hw)
  rw [List.range_eq_range'] at hf
  have hf' : (List.range' 0 30).foldlM tieTurn (#[w.row], w.sEnd + 1, #[w.sEnd + 2]) F1 t1 =
      some (s, _, _) := hf
  have K : Gives (fun (x : Array Aff × Nat × Array Nat) (b : TieStep) =>
        b = ⟨x.1, w.sEnd, x.2.1, x.2.2⟩)
      ((List.range' 0 30).foldlM tieTurn (#[w.row], w.sEnd + 1, #[w.sEnd + 2]))
      ((List.range' 1 30).foldlM (lkTieStep a) ⟨#[w.row], w.sEnd, w.sEnd + 1, #[w.sEnd + 2]⟩) := by
    refine Gives.foldRange _ _ 30
      (fun _ (x : Array Aff × Nat × Array Nat) (b : TieStep) => b = ⟨x.1, w.sEnd, x.2.1, x.2.2⟩)
      0 1 _ _ ?_ rfl
    intro i x b _ hb F' t' y G' u' e
    have hb' : b = ⟨x.1, w.sEnd, x.2.1, x.2.2⟩ := hb
    subst hb'
    unfold tieTurn at e
    obtain ⟨w', F3, t3, hw', e⟩ := bindS e
    obtain ⟨e1, e2, e3⟩ := pureS e
    subst e1 e2 e3
    exact ⟨_, cut_tieStep (a := a) (s := ⟨x.1, w.sEnd, x.2.1, x.2.2⟩) (j := 1 + i) (by omega)
      (whole_ok hw'), rfl⟩
  obtain ⟨b, hb, e⟩ := K _ _ _ _ _ hf'
  subst e
  refine ⟨⟨s.1, w.sEnd, s.2.1, s.2.2⟩, ?_, rfl⟩
  rw [range31, List.foldlM_cons]
  exact bindM h0 hb

/-- **The tie, and the point that joins the roots of the planes.** -/
theorem tie_lkTie {a : E} {F G G' : Fork} {t u u' : Tape} {rows : Array Aff} {sZ : Nat}
    {sG : Array Nat} {y : Array E} (h : K3.tie a F t = some ((rows, sZ, sG), G, u))
    (hp : Fl.point .lkpPlanes 5 G u = some (y, G', u')) :
    lkTie a F t =
      some ({ rows := rows, sZ := sZ, rhoT := y.reverse,
              cT := (List.range 32).foldl
                (fun (f : Aff) j =>
                  Aff.addMul f (Aff.slot (sG.getD j 0)) ((eqTab y.reverse).getD j zeroE))
                (Aff.ofConst zeroE) }, G', u') := by
  obtain ⟨s, hs, e⟩ := tie_fold h
  cases e
  unfold lkTie
  exact bindM hs (bindM hp rfl)

/-- **The bits' sumcheck**: the five lines of `lkPad`, from the course of the masked sumcheck. -/
theorem cut_bits {zs : List E} {m : Nat} (hm : zs.length = m) {F G : Fork} {t u : Tape}
    {w : Whole}
    (h : WholeCut (Aff.ofConst zeroE) zs 2 1
      (fun x => subE (mulE (x.getD 0 zeroE) (x.getD 0 zeroE)) (x.getD 0 zeroE)) F t w G u) :
    ∃ (b0 : Psc) (F0 : Fork) (t0 : Tape) (b1 : Psc) (F1 : Fork) (t1 : Tape) (b2 : Psc) (F2 : Fork)
      (t2 : Tape) (vBit : E) (b3 : Psc),
      Fl.pscBegin (Aff.ofConst zeroE) F t = some (b0, F0, t0) ∧
      Fl.roundsIn .eq2 b0 (zs.map fun z => (z, 0)) F0 t0 =
        some (((w.challenges.take m).toArray, b1), F1, t1) ∧
      Fl.pscEnds b1 2 1 F1 t1 = some ((w.sEnd, b2), F2, t2) ∧
      Fl.shown w.sEnd F2 t2 = some (vBit, F2, t2) ∧
      Fl.pscRow b2 (subE (mulE vBit vBit) vBit) {} F2 t2 = some ((w.row, b3), G, u) := by
  obtain ⟨p0, F0, t0, p1, F1, t1, p2, F2, t2, ends, p3, h0, h1, h2, hs, h4, hc⟩ := h
  obtain ⟨cs, hl, hcs, hR⟩ := rounds_bits zs #[] p0 F0 t0 p1 F1 t1 h1
  obtain ⟨beta, hb⟩ := ends_r h2
  have hch : w.challenges.take m = cs := by
    have k : (([] : List E) ++ cs ++ [beta]).take m = cs := by
      rw [List.nil_append, ← hm, ← hl]
      exact List.take_left' rfl
    rw [hc, hb, Array.toList_push, hcs, begin_r h0]
    exact k
  refine ⟨p0, F0, t0, p1, F1, t1, p2, F2, t2, ends.getD 0 zeroE, p3, h0, ?_, h2,
    shownM (hs 0 (by omega)) _, h4⟩
  rw [roundsIn_def, hch]
  exact hR

/-- The same from the stand-in's yes. -/
theorem whole_bits {zs : List E} {m : Nat} (hm : zs.length = m) {F G : Fork} {t u : Tape}
    {w : Whole}
    (h : wholeStandIn (Aff.ofConst zeroE) zs 2 1
      (fun x => subE (mulE (x.getD 0 zeroE) (x.getD 0 zeroE)) (x.getD 0 zeroE)) F t =
      some (w, G, u)) :
    ∃ (b0 : Psc) (F0 : Fork) (t0 : Tape) (b1 : Psc) (F1 : Fork) (t1 : Tape) (b2 : Psc) (F2 : Fork)
      (t2 : Tape) (vBit : E) (b3 : Psc),
      Fl.pscBegin (Aff.ofConst zeroE) F t = some (b0, F0, t0) ∧
      Fl.roundsIn .eq2 b0 (zs.map fun z => (z, 0)) F0 t0 =
        some (((w.challenges.take m).toArray, b1), F1, t1) ∧
      Fl.pscEnds b1 2 1 F1 t1 = some ((w.sEnd, b2), F2, t2) ∧
      Fl.shown w.sEnd F2 t2 = some (vBit, F2, t2) ∧
      Fl.pscRow b2 (subE (mulE vBit vBit) vBit) {} F2 t2 = some ((w.row, b3), G, u) :=
  cut_bits hm (whole_ok h)

end VerifiableInference.Desc.K3Cut
