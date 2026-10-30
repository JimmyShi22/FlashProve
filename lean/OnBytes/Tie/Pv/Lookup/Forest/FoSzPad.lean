-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoSzPad.lean.
The rounds of a run of Forest.pad have the sizes of the flat function's plan.

The flat function of a sub-proof's lookup cuts plain data into rounds by a plan: for each round the
number of elements sent and the number drawn (Fo.planF, from the public shape alone). This file
shows that a run of the byte-level routine Forest.pad on a view that returns takes rounds of exactly
these sizes off the view.

States, each for a run that returns, from a clean context:
  sz_draws: the shift's round, if there are several calls, and alpha's.
  sz_step, sz_tie: a step of the tie; the 31 steps and the point of five.
  sz_level: a level of a tree with mu variables, with the line's draw.
  sz_begin, sz_vars, sz_ends, sz_point: the pieces of a sumcheck; a point.
  sz_leaves, sz_bits: the degrees of the leaves' and the bits' rounds are the plan's.
  pad_sizes: along the chain of Fo.PadCut: SzOn c c' (planF h).
  pad_sizes_view, pad_sizes_any: so the rounds of the view between the two contexts, and every row
    of rounds that leads from the one to the other, under every reading, have the plan's sizes.
Premise: the context is clean (a view, no message open).

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoSz
import OnBytes.Tie.Pv.Lookup.Forest.FoPadCut
import OnBytes.Tie.Pv.Lookup.Forest.FoDraws
import OnBytes.Tie.Pv.Lookup.Forest.FoTieRun
import OnBytes.Tie.Pv.Lookup.Forest.FoLevelLaw
import OnBytes.Tie.Pv.Lookup.Forest.FoR5Run
import OnBytes.Tie.Pv.Lookup.Forest.FoV

set_option autoImplicit false

namespace Fo
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun

/-! ### The pieces -/

theorem sz_point {r : RoundName} {n : ℕ} {F G : Fork} {c c' : Ctx} {v : Array E}
    (h : SubM.point r n F c = .ok ((v, G), c')) (hc : Clean c) :
    SzOn c c' [(0, n)] ∧ v.size = n := by
  obtain ⟨he, _⟩ := (point_ok r n F G c c' v).1 h
  obtain ⟨_, _, _, _, hs⟩ := round_point r n v c c' hc he
  exact ⟨⟨_, he, .point r n v .nil, by show [(0, v.size)] = _; rw [hs]⟩, hs⟩

theorem sz_begin {C : Aff} {F G : Fork} {c c' : Ctx} {p : Psc}
    (h : pscBegin C F c = .ok ((p, G), c')) : SzOn c c' [(1, 1)] := by
  obtain ⟨_, mu, eps, _, he, _⟩ := pscBegin_ok C F G c c' p h
  exact ⟨_, he, .sum mu _ eps .nil, rfl⟩

theorem rds_vars : ∀ (zd : List (E × ℕ)) (rs : List (Array E × E)), Rds (evVars zd rs)
  | [], _ => .nil
  | _ :: _, [] => .nil
  | p :: zd, r :: rs => .read (p.2 - 1) r.1 .pscRound r.2 (rds_vars zd rs)

theorem szEv_vars : ∀ (zd : List (E × ℕ)) (rs : List (Array E × E)), FitsA zd rs →
    szEv (evVars zd rs) = zd.map fun p => (p.2 - 1, 1)
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | p :: zd, r :: rs, h => by
    show (0 + r.1.size, 1) :: szEv (evVars zd rs) = (p.2 - 1, 1) :: _
    rw [szEv_vars zd rs h.2, ← h.1]
    simp

theorem sz_vars {form : RoundForm} (hf : form.equality = true) {p p' : Psc} {zs : List (E × ℕ)}
    {F G : Fork} {c c' : Ctx} {r : Array E}
    (h : roundsIn form p zs F c = .ok (((r, p'), G), c')) :
    SzOn c c' (zs.map fun z => (roundValues form z.2, 1)) := by
  obtain ⟨rs, a1, a2, _⟩ := roundsIn_ok form hf p zs F G c c' r p' h
  refine ⟨_, a2, rds_vars _ _, ?_⟩
  rw [szEv_vars _ _ a1]
  unfold zdOf
  rw [List.map_map]
  rfl

theorem sz_ends {p p' : Psc} {dY n e : ℕ} {F G : Fork} {c c' : Ctx}
    (h : pscEnds p dY n F c = .ok (((e, p'), G), c')) : SzOn c c' [(dY, 1), (n, 0)] := by
  obtain ⟨sent, beta, v, _, _, _, s1, s2, he, _⟩ := pscEnds_ok p dY n F G c c' e p' h
  refine ⟨_, he, .readNZ dY sent _ beta (.values n v _ .nil), ?_⟩
  show [(0 + sent.size, 1), (0 + v.size, 0)] = _
  rw [s1, s2]
  simp

/-! ### The stretches -/

theorem sz_draws {h : Sh} {F G : Fork} {c c' : Ctx} {θ α a : E}
    (hr : Forest.draws h F c = .ok (((θ, α, a), G), c')) :
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
    {c c' : Ctx} (h : Forest.tieStep a s j F c = .ok ((s', G), c')) :
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

theorem sz_tie (S : TwNums.Sizes) {a : E} {F G : Fork} {c c' : Ctx} {T : Forest.Tie}
    (h : Forest.tie a F c = .ok ((T, G), c')) (hc : Clean c) :
    SzOn c c' ((List.range 31).flatMap (fun j => scRounds (S.scTie j)) ++ [(0, 5)]) := by
  obtain ⟨s, c1, pt, h1, h2, _⟩ := tie_ok a F G c c' T h
  have z1 := foldlM_sz (Forest.tieStep a) (fun j => scRounds (S.scTie j))
    (fun _ _ _ _ _ _ _ hs _ => sz_step S hs) _ _ _ _ _ _ _ h1 hc
  obtain ⟨_, _, _, _, hs⟩ := round_point _ _ _ _ _ (z1.clean hc) h2
  exact z1.append ⟨_, h2, .point _ 5 pt .nil, by show [(0, pt.size)] = _; rw [hs]⟩

theorem szEv_lvEv : ∀ rs : List (Array E × E), (∀ q ∈ rs, q.1.size = 2) →
    szEv (lvEv rs) = List.replicate rs.length (2, 1)
  | [], _ => rfl
  | q :: rs, h => by
    show (0 + q.1.size, 1) :: szEv (lvEv rs) = (2, 1) :: List.replicate rs.length (2, 1)
    rw [szEv_lvEv rs fun x hx => h x (List.mem_cons_of_mem _ hx), h q List.mem_cons_self]

theorem sz_level {s s' : Forest.Descent} {mu : ℕ} {order : List ℕ} {F G : Fork} {c c' : Ctx}
    (h : Forest.level s mu order F c = .ok ((s', G), c')) :
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

/-! ### The degrees of the last two sumchecks -/

theorem sz_leaves (h : Sh) (rho : Array E) :
    [(1, 1)] ++ (((List.range (5 + h.d)).map fun j =>
        (rho.getD j zeroE, if j < h.d then 2 else 1)).map fun z => (roundValues .eq z.2, 1)) =
      scRounds (S h).scEnd := by
  show _ = (1, 1) :: ((List.range (FoNums.w + h.d)).reverse.map
    fun t => if t < FoNums.w then 1 else 2).map (fun n => (n, 1)) ++ []
  rw [List.append_nil, List.map_map, List.map_map, List.singleton_append]
  congr 1
  refine List.ext_getElem (by simp [FoNums.w]) fun i h1 h2 => ?_
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_range,
    Function.comp, roundValues, FoNums.w]
  by_cases hi : i < h.d
  · rw [if_pos hi, if_neg (by omega)]
  · rw [if_neg hi, if_pos (by omega)]

theorem sz_bits (h : Sh) (pt : Array E) (hp : pt.size = 5 + h.d) :
    [(1, 1)] ++ ((pt.reverse.toList.map fun z => (z, 0)).map
        fun z : E × ℕ => (roundValues .eq2 z.2, 1)) ++ [(2, 1), (1, 0)] =
      scRounds (S h).scBit := by
  have e : ((pt.reverse.toList.map fun z => (z, 0)).map
      fun z : E × ℕ => (roundValues .eq2 z.2, 1)) = List.replicate (5 + h.d) (2, 1) := by
    rw [List.map_map, ← hp]
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp [roundValues]
  rw [e]
  simp [scRounds, TwNums.Sizes.scBit, FoNums.S, FoNums.w, List.map_replicate]

/-! ### The whole run -/

/-- **The rounds of a run of Forest.pad have the plan's sizes.** -/
theorem pad_sizes {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Ctx}
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
  have c7 : M.d7 = M.d6 := congrArg (fun x : (E × Fork) × Ctx => x.2) e7
  obtain ⟨_, _, _, _, c8, _⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ P.l8
  have yL := y1.append y2
  rw [sz_leaves] at yL
  have yB := (y4.append y5).append y6
  rw [sz_bits (M.h pub) M.pt hp] at yB
  have all := (((((z1.append z2).append z3).append z4).append yL).append y3).append yB
  rw [P.ctx, c8, c7]
  unfold planF
  simpa only [List.append_assoc] using all

theorem pad_sizes_view {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Ctx}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) (hc : Clean c)
    {rv : List Fmt.RoundView} (ht : Took c rv c') :
    rv.map (fun r => ((sentOf r).length, (drawnOf r).length)) = planF (M.h pub) :=
  (pad_sizes P hc).view hc ht

theorem pad_sizes_any {K : Type} [CommRing K] (ρ : Reading K) {calls : Array Call}
    {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Ctx} {g : Forest.Heard} {M : PadMid}
    (P : PadCut calls pub lid F c g F' c' M) (hc : Clean c) {l : List Ev} (hl : Rds l)
    (he : Evs l c c') :
    (flEv ρ l).map (fun r => (r.1.length, r.2.length)) = planF (M.h pub) :=
  (pad_sizes P hc).any ρ hc hl he

end Fo
