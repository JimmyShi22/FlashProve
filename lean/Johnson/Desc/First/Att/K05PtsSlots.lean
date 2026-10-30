-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PtsSlots.lean: kind K5: ALONG EVERY STRETCH THAT THE RUNS OF CLAIMS WALK FROM
A NUMBER OF WHAT WAS HEARD, THE SLOTS ARE FILLED BEHIND THE HEARING: the premise PtsSlots of
Att/Claims/SlotsIn.lean is a lemma, at Ps := "slot j is filled in the ledger G of which Said speaks",
under one record of tests on public data (GeoFits).

Main names:
  `K5Law.foldlM_first`, `K5Law.planes_members`: what pointsOf (Att/Points.lean) lays into its FIRST list:
    EVERY MEMBER has np = 3 and the number of a remainder unit, or np = 5 and the number of a softmax
    unit's seven. (Att/Claims/PlanesAre.lean: planes_are says what lies at which INDEX; that
    the list has no further member it does not say.)
  `GeoFits g x`: PUBLIC: the place's numbers and the plan's record of rounds agree: lt, NP = pairs,
    Lam; every softmax unit has at most `pairs` pieces; every entry of x.score counts `pairs`.
  `geoFitsB`, `geoFits_of_B`: the same as a Bool.
  `planesAt_fl`, `units_fl`: what Said says lies under the units' scalars and end values.
  `pts_slots`: **Said x h G L · pointsOf g zk h l = some p · GeoFits g x give PtsSlots (PscRun.Filled G) g p.**
  `geoFits_bites`: a control: a plan whose lt is another has not GeoFits.
Premises: those three.
Limits. GeoFits IS SHOWN OF NO PLAN HERE: five tests on public numbers; at recOf P rows
(OnBytes/Tie/Pv/Att/OwnAtFits.lean) every entry of score counts P.D.nb = pairs by that text. EMPTY
AT: a hearing of which Said does not hold.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05RowsSlots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Pts Geo Heard Left RemP ScoreP UnitG CallG)
open VerifiableInference.Desc.Part

/-- A fold that pushes one plane claim and one unit a step: what lies in the first list. -/
theorem foldlM_first {X : Type}
    (step : Array RemP × Array ScoreP → X → Option (Array RemP × Array ScoreP))
    (Q : RemP → X → Prop)
    (hstep : ∀ acc x acc1, step acc x = some acc1 →
      ∃ rem k, acc1 = (acc.1.push rem, acc.2.push k) ∧ Q rem x) :
    ∀ (xs : List X) (acc acc' : Array RemP × Array ScoreP), xs.foldlM step acc = some acc' →
      ∀ pc ∈ acc'.1.toList, pc ∈ acc.1.toList ∨ ∃ x ∈ xs, Q pc x
  | [], acc, acc', h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact fun pc hpc => .inl hpc
  | x :: xs, acc, acc', h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨acc1, h1, h2⟩ := h
    obtain ⟨rem, k, e, hQ⟩ := hstep acc x acc1 h1
    intro pc hpc
    rcases foldlM_first step Q hstep xs acc1 acc' h2 pc hpc with h3 | ⟨y, hy, hq⟩
    · subst e
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at h3
      rcases h3 with h3 | rfl
      · exact .inl h3
      · exact .inr ⟨x, List.mem_cons_self .., hQ⟩
    · exact .inr ⟨y, List.mem_cons_of_mem _ hy, hq⟩

/-- **What pointsOf lays into its first list.** -/
theorem planes_members {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : P.pointsOf g zk h L = some p) : ∀ pc ∈ p.planes.toList,
      (pc.np = 3 ∧ pc.s0 ∈ h.remainders.toList) ∨ (pc.np = 5 ∧ ∃ o ∈ h.scores.toList, pc.s0 = o.1) := by
  unfold P.pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, hn, a, hf, uW, _, uX, _, uH, _, _, hs, _, _, e⟩ := hp
  rw [← Array.foldlM_toList] at hf
  have hq := foldlM_first _
    (fun (pc : RemP) (x : (UnitG × ℕ × MaskedSum.Heard) × Aff) => pc.np = 5 ∧ pc.s0 = x.1.2.1)
    (fun acc x acc1 h1 => by
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at h1
      obtain ⟨_, _, e1⟩ := h1
      exact ⟨_, _, e1.symm, rfl, rfl⟩) _ _ _ hf
  subst e
  intro pc hpc
  rcases hq pc hpc with h1 | ⟨x, hx, e5, e0⟩
  · left
    simp only [Array.toList_map, List.mem_map] at h1
    obtain ⟨y, hy, rfl⟩ := h1
    rw [Array.toList_zip] at hy
    exact ⟨rfl, (List.of_mem_zip hy).2⟩
  · right
    rw [Array.toList_zip] at hx
    have h2 := (List.of_mem_zip hx).1
    rw [Array.toList_zip] at h2
    exact ⟨e5, x.1.2, (List.of_mem_zip h2).2, e0⟩

end K5Law

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.Part
open K5Law (PtsSlots PointsAre points_are planes_members)

/-- PUBLIC: the place's numbers and the plan's record of rounds agree. -/
structure GeoFits (g : Geo) (x : Params.AttentionRounds) : Prop where
  lt : g.lt = x.lt
  NP : g.NP = x.pairs
  Lam : g.Lam = x.Lam
  pieces : ∀ u ∈ g.scores, u.pcs.length ≤ x.pairs
  score : ∀ t ∈ x.score, t.2 = x.pairs

/-- The same as a Bool: a test on public data that a program can run. -/
def geoFitsB (g : Geo) (x : Params.AttentionRounds) : Bool :=
  g.lt == x.lt && g.NP == x.pairs && g.Lam == x.Lam &&
    (g.scores.all fun u => Decidable.decide (u.pcs.length ≤ x.pairs)) && x.score.all fun t => t.2 == x.pairs

theorem geoFits_of_B {g : Geo} {x : Params.AttentionRounds} (h : geoFitsB g x = true) :
    GeoFits g x := by
  unfold geoFitsB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem planesAt_fl {G : Fork} : ∀ (js : List ℕ) (vs : List (List E)), PlanesAt js vs G →
    ∀ j ∈ js, ∀ i, i < 3 → PscRun.Filled G (j + i)
  | [], [], _ => fun _ hj => by cases hj
  | j :: js, v :: vs, ⟨a1, a2, a3⟩ => fun j' hj i hi => by
    rcases List.mem_cons.1 hj with rfl | hj
    · exact putRun_fl a2 i (by rw [a1]; exact hi)
    · exact planesAt_fl js vs a3 j' hj i hi
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem units_fl {G : Fork} : ∀ (ps : List (ℕ × ℕ)) (os : List (ℕ × MaskedSum.Heard)) (pre : List E)
    (l : List (List E × OnBytes.Tie.Pv.Att.PscH)), UnitsAt ps os pre l G → ∀ o ∈ os,
      (∀ i, i < 7 → PscRun.Filled G (o.1 + i)) ∧ ∃ t ∈ ps, ∀ i, i < 2 * t.2 → PscRun.Filled G (o.2.sEnd + i)
  | [], [], _, [], _ => fun _ ho => by cases ho
  | u :: ps, o :: os, _, (_, _) :: l, ⟨a1, a2, a3, _, a5⟩ => fun o' ho => by
    rcases List.mem_cons.1 ho with rfl | ho
    · exact ⟨fun i hi => putRun_fl a2 i (by rw [a1]; exact hi), u, List.mem_cons_self ..,
        sumAt_ends a3⟩
    · obtain ⟨b1, t, ht, b2⟩ := units_fl ps os [] l a5 o' ho
      exact ⟨b1, t, List.mem_cons_of_mem _ ht, b2⟩
  | [], [], _, _ :: _, h => h.elim
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | _ :: _, _ :: _, _, [], h => h.elim

theorem piecesOf_size (u : UnitG) (zk : Array E) : (piecesOf u zk).size = u.pcs.length := by
  unfold piecesOf
  simp

/-- **PtsSlots is a lemma.** -/
theorem pts_slots {g : Geo} {zk : Array (Array E)} {h : Heard} {l : Left} {p : Pts} {G : Fork}
    {x : Params.AttentionRounds} {L : Lists} (hs : Said x h G L) (hp : pointsOf g zk h l = some p)
    (gf : GeoFits g x) : PtsSlots (PscRun.Filled G) g p := by
  have H := points_are hp
  refine ⟨fun pc hpc => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases planes_members hp pc hpc with ⟨e3, hm⟩ | ⟨e5, o, ho, e0⟩
    · rw [e3]
      exact ⟨Nat.le_refl _, planesAt_fl _ _ hs.planes _ hm⟩
    · rw [e5, e0]
      exact ⟨by omega, fun i hi => (units_fl _ _ _ _ hs.units o ho).1 i (by omega)⟩
  · obtain ⟨⟨⟨u, o⟩, f⟩, hx, ⟨hsc, _, h0, hpw⟩, _⟩ := forall2_left H.units k hk
    rw [Array.toList_zip] at hx
    have h1 := (List.of_mem_zip hx).1
    rw [Array.toList_zip] at h1
    have ho : o ∈ h.scores.toList := (List.of_mem_zip h1).2
    have hu : u ∈ g.scores := by simpa using (List.of_mem_zip h1).1
    obtain ⟨b1, t, ht, b2⟩ := units_fl _ _ _ _ hs.units o ho
    rw [h0, hsc, hpw, piecesOf_size]
    refine ⟨b1, fun i hi => b2 i ?_⟩
    have hi' : i < 2 * u.pcs.length := hi
    have := gf.pieces u hu
    rw [gf.score t ht]
    omega
  · rw [H.s5]
    exact fun i hi => putRun_fl hs.p5 i (by rw [hs.l5]; exact hi)
  · rw [H.sIB, gf.lt]
    exact fun i hi => putRun_fl hs.pI i (by rw [hs.lI]; exact hi)
  · rw [H.s5h]
    exact fun i hi => putRun_fl hs.p2 i (by rw [hs.l2]; exact hi)
  · rw [H.sCl]
    exact fun i hi => putRun_fl hs.pC i (by rw [hs.lC]; exact hi)
  · rw [H.sM6, gf.NP]
    exact fun i hi => putRun_fl hs.pM i (by rw [hs.lM]; exact hi)
  · rw [H.scE, gf.NP]
    exact sumAt_ends hs.sE
  · rw [H.vpm, gf.NP]
    exact sumAt_ends hs.sM
  · rw [H.vpd, gf.NP]
    exact sumAt_ends hs.sVD
  · rw [H.scF, gf.NP]
    exact sumAt_ends hs.sF
  · rw [H.scd, gf.NP, gf.Lam, gf.lt]
    exact sumAt_endsKey hs.sD
  · rw [H.scH, gf.NP]
    exact sumAt_ends hs.sH

/-- A control. -/
theorem geoFits_bites {g : Geo} {x : Params.AttentionRounds} (h : g.lt ≠ x.lt) : ¬ GeoFits g x :=
  fun a => h a.lt

end VerifiableInference.Desc.First.Att.P

#print axioms K5Law.planes_members
#print axioms VerifiableInference.Desc.First.Att.P.units_fl
#print axioms VerifiableInference.Desc.First.Att.P.pts_slots
#print axioms VerifiableInference.Desc.First.Att.P.geoFits_bites
