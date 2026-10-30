-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoSzPad.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoSzPad.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  sz_point, sz_begin, sz_vars, sz_ends, sz_draws, sz_step, sz_tie, sz_level, pad_sizes,
  pad_sizes_view, pad_sizes_any
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  Sizes, drawnOf, drawsEv, flEv, levelEv, planF, rds_level, rds_lvEv, rds_vars, scRounds, scTie,
  sentOf, several, szEv_append, szEv_lvEv, szEv_vars, sz_bits, sz_leaves, zdOf
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoSzPad
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.FoR5Run
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoPscForm
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoLevel
import Johnson.Top.H.FlPort.FoRds
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.FoLevelRun
import Johnson.Top.H.FlPort.FoDraws
import Johnson.Top.H.FlPort.FoPadCut
import Johnson.Top.H.FlPort.FoSz
import Johnson.Top.H.FlPort.FoLevelLaw

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun

theorem sz_point {r : RoundName} {n : ℕ} {F G : Fork} {c c' : Tape} {v : Array E}
    (h : Fl.point r n F c = .ok ((v, G), c')) (hc : Clean c) :
    SzOn c c' [(0, n)] ∧ v.size = n := by
  obtain ⟨he, _⟩ := (point_ok r n F G c c' v).1 h
  obtain ⟨_, _, _, _, hs⟩ := round_point r n v c c' hc he
  exact ⟨⟨_, he, .point r n v .nil, by show [(0, v.size)] = _; rw [hs]⟩, hs⟩

theorem sz_begin {C : Aff} {F G : Fork} {c c' : Tape} {p : Psc}
    (h : Fl.pscBegin C F c = .ok ((p, G), c')) : SzOn c c' [(1, 1)] := by
  obtain ⟨_, mu, eps, _, he, _⟩ := pscBegin_ok C F G c c' p h
  exact ⟨_, he, .sum mu _ eps .nil, rfl⟩

theorem sz_vars {form : RoundForm} (hf : form.equality = true) {p p' : Psc} {zs : List (E × ℕ)}
    {F G : Fork} {c c' : Tape} {r : Array E}
    (h : Fl.roundsIn form p zs F c = .ok (((r, p'), G), c')) :
    SzOn c c' (zs.map fun z => (roundValues form z.2, 1)) := by
  obtain ⟨rs, a1, a2, _⟩ := roundsIn_ok form hf p zs F G c c' r p' h
  refine ⟨_, a2, rds_vars _ _, ?_⟩
  rw [szEv_vars _ _ a1]
  unfold zdOf
  rw [List.map_map]
  rfl

theorem sz_ends {p p' : Psc} {dY n e : ℕ} {F G : Fork} {c c' : Tape}
    (h : Fl.pscEnds p dY n F c = .ok (((e, p'), G), c')) : SzOn c c' [(dY, 1), (n, 0)] := by
  obtain ⟨sent, beta, v, _, _, _, s1, s2, he, _⟩ := pscEnds_ok p dY n F G c c' e p' h
  refine ⟨_, he, .readNZ dY sent _ beta (.values n v _ .nil), ?_⟩
  show [(0 + sent.size, 1), (0 + v.size, 0)] = _
  rw [s1, s2]
  simp

theorem sz_draws {h : Sh} {F G : Fork} {c c' : Tape} {θ α a : E}
    (hr : lkDraws h F c = .ok (((θ, α, a), G), c')) :
    SzOn c c' ((if several h then [(0, 1)] else []) ++ [(0, 1)]) := by
  obtain ⟨he, _⟩ := draws_ok h F G c c' θ α a hr
  unfold drawsEv at he
  unfold several
  by_cases hN : h.NC > 1
  · rw [if_pos hN] at he
    rw [if_pos (by simpa using hN)]
    exact ⟨_, he, .ans _ θ (.ans _ α .nil), rfl⟩
  · rw [if_neg hN] at he
    rw [if_neg (by simpa using hN)]
    exact ⟨_, he, .ans _ α .nil, rfl⟩

theorem sz_step (S : TwNums.Sizes) {a : E} {s s' : Forest.TieStep} {j : ℕ} {F G : Fork}
    {c c' : Tape} (h : lkTieStep a s j F c = .ok ((s', G), c')) :
    SzOn c c' (scRounds (S.scTie j)) := by
  obtain ⟨_, mu, eps, sent, beta, v, _, _, _, _, _, he, s1, s2, _⟩ :=
    tieStep_ok a s j F G c c' s' h
  refine ⟨_, he, .sum mu _ eps (.readNZ 3 sent _ beta (.values _ v _ .nil)), ?_⟩
  show [(0 + 1, 1), (0 + sent.size, 1), (0 + v.size, 0)] = _
  rw [s1, s2]
  by_cases hj : j = 0
  · subst hj
    rfl
  · simp [scRounds, TwNums.Sizes.scTie, hj]

theorem sz_tie (S : TwNums.Sizes) {a : E} {F G : Fork} {c c' : Tape} {T : Forest.Tie}
    (h : lkTie a F c = .ok ((T, G), c')) (hc : Clean c) :
    SzOn c c' ((List.range 31).flatMap (fun j => scRounds (S.scTie j)) ++ [(0, 5)]) := by
  obtain ⟨s, c1, pt, h1, h2, _⟩ := tie_ok a F G c c' T h
  have z1 := foldlM_sz (lkTieStep a) (fun j => scRounds (S.scTie j))
    (fun _ _ _ _ _ _ _ hs _ => sz_step S hs) _ _ _ _ _ _ _ h1 hc
  obtain ⟨_, _, _, _, hs⟩ := round_point _ _ _ _ _ (z1.clean hc) h2
  exact z1.append ⟨_, h2, .point _ 5 pt .nil, by show [(0, pt.size)] = _; rw [hs]⟩

theorem sz_level {s s' : Forest.Descent} {mu : ℕ} {order : List ℕ} {F G : Fork} {c c' : Tape}
    (h : lkLevel s mu order F c = .ok ((s', G), c')) :
    SzOn c c' (scRounds ⟨List.replicate mu 2 ++ [2], true, 2⟩ ++ [(0, 1)]) := by
  obtain ⟨o, h1, _⟩ := level_ok s mu order F G c c' s' h
  obtain ⟨_, m0, eps, rs, sentY, beta, vals, _, _, _, _, a1, _, _, a2, _, a3, a4, a5, he, _⟩ :=
    levelIn_ran mu s.rho s.form order F G c c' o h1
  refine ⟨_, he, rds_level m0 eps rs sentY beta vals o.tau, ?_⟩
  unfold levelEv
  rw [szEv_append (.sum m0 _ eps .nil), szEv_append (by simpa using rds_lvEv rs .nil),
    szEv_lvEv rs a3, a2, a1]
  show [(0 + 1, 1)] ++ (List.replicate mu (2, 1) ++
    [(0 + sentY.size, 1), (0 + vals.size, 0), (0, 1)]) = _
  rw [a4, a5]
  simp [scRounds, List.map_replicate]

/-- **The rounds of a run of lkPad have the plan's sizes.** -/
theorem pad_sizes {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) (hc : Clean c) :
    SzOn c c' (planF (M.h pub)) := by
  have z1 := sz_draws P.draws
  have k1 := z1.clean hc
  have z2 := sz_tie (S (M.h pub)) P.tie k1
  have k2 := z2.clean k1
  have z3 := foldlM_sz _ (fun l => scRounds ((S (M.h pub)).scKey l) ++ [(0, 1)])
    (fun _ _ _ _ _ _ _ hs _ => sz_level hs) _ _ _ _ _ _ _ P.keys k2
  have k3 := z3.clean k2
  have z4 := foldlM_sz _ (fun l => scRounds ((S (M.h pub)).scTab l) ++ [(0, 1)])
    (fun _ _ _ _ _ _ _ hs _ => sz_level hs) _ _ _ _ _ _ _ P.table k3
  have k4 := z4.clean k3
  have y1 := sz_begin P.l1
  have y2 := sz_vars rfl P.l2
  have k5 := y2.clean (y1.clean k4)
  obtain ⟨y3, hp⟩ := sz_point P.l3 k5
  have y4 := sz_begin P.l4
  have y5 := sz_vars rfl P.l5
  have y6 := sz_ends P.l6
  obtain ⟨_, _, e7⟩ := (shown_ok _ _ _ _).1 P.l7
  have c7 : M.d7 = M.d6 := congrArg (fun x : (E × Fork) × Tape => x.2) e7
  obtain ⟨_, _, _, _, c8, _⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ P.l8
  have yL := y1.append y2
  rw [sz_leaves] at yL
  have yB := (y4.append y5).append y6
  rw [sz_bits (M.h pub) M.pt hp] at yB
  have all := (((((z1.append z2).append z3).append z4).append yL).append y3).append yB
  rw [P.ctx, c8, c7]
  unfold planF
  simpa only [List.append_assoc] using all

theorem pad_sizes_view {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) (hc : Clean c)
    {rv : List FlatRound} (ht : Took c rv c') :
    rv.map (fun r => ((sentOf r).length, (drawnOf r).length)) = planF (M.h pub) :=
  (pad_sizes P hc).view hc ht

theorem pad_sizes_any {K : Type} [CommRing K] (ρ : Reading K) {calls : Array Call}
    {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape} {g : Forest.Heard} {M : PadMid}
    (P : PadCut calls pub lid F c g F' c' M) (hc : Clean c) {l : List Ev} (hl : Rds l)
    (he : Evs l c c') :
    (flEv ρ l).map (fun r => (r.1.length, r.2.length)) = planF (M.h pub) :=
  (pad_sizes P hc).any ρ hc hl he


end Fo.Tp
