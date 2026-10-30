-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/Seams.lean: what attention's two kinds of sumcheck have heard and done where
their routines succeed, and that the summand which the port computes is the function on plain data.

sc3In, sc3Shown and scdIn are routines of OnBytes/Model/AttentionSums.lean; keyTerm is one of
OnBytes/Model/AttentionDivide.lean.

Main names:
  `sc3In_seam`, `scdIn_seam`: if the routine that receives a sumcheck's messages succeeds from a
    state whose arrays on slots have their length, then: the start's public part is the target; the
    rounds heard are PSC epsilon with one scalar, the rounds of the variables, PSC Y, PSC values
    (`Parts`, with no further scalar); the sumcheck's record is that of these rounds (`Ended`:
    running claim, weights, challenges, hiding walk); the record's r holds the challenges of the
    variables in the order of the rounds; each round has as many scalars as its degree says; sEnd is
    the slot behind the scalars of the rounds; the end values were put under the slots from sEnd on
    with the factor beta (`Filled`).
  `sc3Shown_flat`: where sc3Shown succeeds it leaves state and context as they were and returns
    `sc3Flat` on what the state shows under the slots from sEnd on.
  `keyTerm_flat`: the same of keyTerm and `keyTermFlat`.
  `keyAtIndexIn_flat`: keyAtIndexIn, where it succeeds, is three steps: the draw that batches the
    pairs; scdIn; scdRow at `keyFlat` on what the state shows under the slots from sEnd on.

Limits: one direction: from the routine's success. On a view and in the dry run alike. Nothing is
said on what the caller does with the record.
-/
import OnBytes.Model.AttentionDivide
import OnBytes.Tie.Pv.Psc.Run.PscSeam
import OnBytes.Tie.Pv.Att.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Attention
open OnBytes.Psc (Weight hearMany)

theorem plain_sizes (ds : List Nat) :
    (ds.map fun d => Weight.plain (d + 1)).map (fun w => w.d - 1) = ds := by
  rw [List.map_map]
  exact List.map_id' ds

/-- Each round has as many scalars as its degree says. -/
theorem sizes_map : ∀ (ds : List Nat) (rs : List (List E × E)), rs.length = ds.length →
    (∀ x ∈ (ds.map fun d => Weight.plain (d + 1)).zip rs, x.2.1.length + 1 = x.1.d) →
    rs.map (·.1.length) = ds
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | d :: ds, r :: rs, h, hs => by
    have h0 : r.1.length + 1 = d + 1 := hs (Weight.plain (d + 1), r) (by simp)
    have h1 := sizes_map ds rs (by simpa using h) fun x hx => hs x (by
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons]
      exact Or.inr hx)
    rw [List.map_cons, h1]
    congr 1
    omega

theorem scdIn_seam (ds : List Nat) (dY n : Nat) (C : Aff) (o : Scd) (F G : Fork) (c c' : Ctx)
    (h : scdIn ds dY n C F c = .ok ((o, G), c')) (hz : Sized F) :
    ∃ (τ mu : E) (rs : List (List E × E)) (sentY : List E) (beta : E) (v : List E),
      F.publicPart C = some τ ∧
      Parts c c c' [] mu o.p.eps (ds.map fun d => Weight.plain (d + 1)) rs dY sentY beta v ∧
      Ended o.p C τ mu o.p.eps F.next (ds.map fun d => Weight.plain (d + 1)) rs dY sentY beta ∧
      o.r.toList = rs.map (·.2) ∧ rs.map (·.1.length) = ds ∧ sentY.length = dY ∧ v.length = n ∧
      1 ≤ dY ∧ 1 ≤ n ∧ (∀ d ∈ ds, 1 ≤ d ∧ d ≤ 64) ∧ o.sEnd = F.next + (1 + ds.sum) + dY ∧
      Filled (taken F (1 + ds.sum + (dY + n))) G o.sEnd v beta := by
  unfold scdIn at h
  obtain ⟨p0, F2, c2, hb, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨x, F3, c3, hr, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨⟨e, p2⟩, G', c4, he, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k3
  obtain ⟨_, _, _, _, _, hF2⟩ := pscBegin_ok C F F2 c c2 p0 hb
  obtain ⟨rs, y, s, r, g, od⟩ := scdRounds_ok ds p0 #[] x F2 F3 c2 c3 hr
  have hF3 : F3 = taken F (1 + ds.sum) := by rw [g, hF2, taken_taken]
  have hm : (hearMany ((ds.map fun d => Weight.plain (d + 1)).map fun w => w.d - 1)).Yields c2 rs
      c3 := by
    rw [plain_sizes]
    exact y
  obtain ⟨τ, mu, sentY, beta, v, a1, _, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
    seam [] C p0 x.2 p2 _ rs dY n e F F2 F3 G' c c c2 c3 c4 (recvEs_zero c) hb hm s he
      (by rw [hF3]; exact sized_taken F _ hz)
  have hp : o.p = p2 := by rw [e1]
  have hε : p2.eps = p0.eps := a5.eps
  refine ⟨τ, mu, rs, sentY, beta, v, a1, ?_, ?_, ?_, ?_, a6, a7, a8, a9, od, ?_, ?_⟩
  · rw [hp, hε, e3]
    exact a3
  · rw [hp, hε]
    exact a5
  · rw [e1]
    show x.1.toList = _
    rw [r]
    rfl
  · exact sizes_map ds rs (by rw [s.len, List.length_map]) s.sizes
  · rw [e1]
    show e = _
    rw [a10, hF3]
    rfl
  · rw [e1, e2]
    show Filled _ G' e v beta
    rw [hF3, taken_taken] at a11
    exact a11

theorem sc3In_seam (nv nb : Nat) (C : Aff) (o : Sc3) (F G : Fork) (c c' : Ctx)
    (h : sc3In nv nb C F c = .ok ((o, G), c')) (hz : Sized F) :
    ∃ (τ mu : E) (rs : List (List E × E)) (sentY : List E) (beta : E) (v : List E),
      F.publicPart C = some τ ∧
      Parts c c c' [] mu o.p.eps (List.replicate nv (Weight.plain 4)) rs 2 sentY beta v ∧
      Ended o.p C τ mu o.p.eps F.next (List.replicate nv (Weight.plain 4)) rs 2 sentY beta ∧
      o.r.toList = rs.map (·.2) ∧ rs.map (·.1.length) = List.replicate nv 3 ∧ sentY.length = 2 ∧
      v.length = 2 * nb ∧
      1 ≤ 2 * nb ∧ o.nb = nb ∧ o.sEnd = F.next + (1 + 3 * nv) + 2 ∧
      Filled (taken F (1 + 3 * nv + (2 + 2 * nb))) G o.sEnd v beta := by
  unfold sc3In at h
  obtain ⟨p0, F2, c2, hb, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨x, F3, c3, hr, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨⟨e, p2⟩, G', c4, he, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k3
  obtain ⟨_, _, _, _, _, hF2⟩ := pscBegin_ok C F F2 c c2 p0 hb
  obtain ⟨rs, y, s, r, g⟩ := sc3Rounds_ok nv p0 #[] x F2 F3 c2 c3 hr
  have hF3 : F3 = taken F (1 + 3 * nv) := by rw [g, hF2, taken_taken]
  have hm : (hearMany ((List.replicate nv (Weight.plain 4)).map fun w => w.d - 1)).Yields c2 rs
      c3 := by
    rw [List.map_replicate]
    exact y
  obtain ⟨τ, mu, sentY, beta, v, a1, _, a3, a4, a5, a6, a7, _, a9, a10, a11⟩ :=
    seam [] C p0 x.2 p2 _ rs 2 (2 * nb) e F F2 F3 G' c c c2 c3 c4 (recvEs_zero c) hb hm s he
      (by rw [hF3]; exact sized_taken F _ hz)
  have hp : o.p = p2 := by rw [e1]
  have hε : p2.eps = p0.eps := a5.eps
  refine ⟨τ, mu, rs, sentY, beta, v, a1, ?_, ?_, ?_, ?_, a6, a7, a9, ?_, ?_, ?_⟩
  · rw [hp, hε, e3]
    exact a3
  · rw [hp, hε]
    exact a5
  · rw [e1]
    show x.1.toList = _
    rw [r]
    rfl
  · refine sizes_map (List.replicate nv 3) rs (by rw [s.len]; simp) ?_
    rw [List.map_replicate]
    exact s.sizes
  · rw [e1]
  · rw [e1]
    show e = _
    rw [a10, hF3]
    rfl
  · rw [e1, e2]
    show Filled _ G' e v beta
    rw [hF3, taken_taken] at a11
    exact a11

/-! ## The summands on a run -/

/-- what a state shows under a slot; 0 if the slot is free -/
def shownAt (F : Fork) (first : Nat) (j : Nat) : E := (F.shown (first + j)).getD zeroE

theorem shown_run (F G : Fork) (c c' : Ctx) (first j : Nat) (x : E)
    (h : SubM.shown (first + j) F c = .ok ((x, G), c')) :
    x = shownAt F first j ∧ G = F ∧ c' = c := by
  obtain ⟨a, b, d⟩ := (ask_ok _ _ _ _ _ _).1 h
  refine ⟨?_, b, d⟩
  unfold shownAt
  rw [a]
  rfl

theorem sc3Shown_flat (o : Sc3) (W : Array E) : ∀ (n b : Nat) (s x : E) (F G : Fork) (c c' : Ctx),
    sc3Shown o W n b s F c = .ok ((x, G), c') →
    x = sc3Flat W (shownAt F o.sEnd) n b s ∧ G = F ∧ c' = c
  | 0, b, s, x, F, G, c, c', h => by
    simp only [sc3Shown] at h
    exact (pure_ok _ _ _ _ _ _).1 h
  | n + 1, b, s, x, F, G, c, c', h => by
    simp only [sc3Shown] at h
    obtain ⟨u, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
    obtain ⟨u1, u2, u3⟩ := shown_run F F1 c c1 o.sEnd (2 * b) u h1
    rw [u2, u3] at k1
    obtain ⟨w, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
    obtain ⟨w1, w2, w3⟩ := shown_run F F2 c c2 o.sEnd (2 * b + 1) w h2
    rw [w2, w3] at k2
    obtain ⟨r1, r2, r3⟩ := sc3Shown_flat o W n (b + 1) _ x F G c c' k2
    rw [sc3Flat_succ, ← u1, ← w1]
    exact ⟨r1, r2, r3⟩

/-- A fold of steps each of which, where it succeeds, leaves state and context as they were and
returns a function of its arguments. -/
theorem foldlM_flat {α : Type} (f : E → α → SubM E) (g : E → α → E) (F : Fork) (c : Ctx)
    (H : ∀ t a x G c', f t a F c = .ok ((x, G), c') → x = g t a ∧ G = F ∧ c' = c) :
    ∀ (l : List α) (t x : E) (G : Fork) (c' : Ctx), l.foldlM f t F c = .ok ((x, G), c') →
      x = l.foldl g t ∧ G = F ∧ c' = c
  | [], t, x, G, c', h => by
    simp only [List.foldlM_nil] at h
    exact (pure_ok _ _ _ _ _ _).1 h
  | a :: l, t, x, G, c', h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨u, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
    obtain ⟨u1, u2, u3⟩ := H t a u F1 c1 h1
    rw [u1, u2, u3] at k1
    exact foldlM_flat f g F c H l _ x G c' k1

theorem keyTerm_flat (S : Shape) (sKC : Nat) (pj : Array E) (w : E) (b : Nat) (x : E) (F G : Fork)
    (c c' : Ctx) (h : keyTerm S sKC pj w b F c = .ok ((x, G), c')) :
    x = keyTermFlat S.cf.lt S.Lam S.HA (shownAt F sKC) pj w b ∧ G = F ∧ c' = c := by
  simp only [keyTerm] at h
  obtain ⟨kc, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨u1, u2, u3⟩ := shown_run F F1 c c1 sKC (b / S.HA) kc h1
  rw [u1, u2, u3] at k1
  refine foldlM_flat _
    (fun t k => mulE t (addE
      (mulE (shownAt F sKC (S.Lam + b * S.cf.lt + k))
        (subE (addE (pj.getD (S.cf.lt - 1 - k) zeroE) (pj.getD (S.cf.lt - 1 - k) zeroE)) oneE))
      (subE oneE (pj.getD (S.cf.lt - 1 - k) zeroE)))) F c ?_ _ _ x G c' k1
  intro t k y G1 c2 h2
  obtain ⟨v, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 h2
  obtain ⟨v1, v2, v3⟩ := shown_run F F3 c c3 sKC (S.Lam + b * S.cf.lt + k) v h3
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k3
  rw [e1, e2, e3, v1, v2, v3]
  exact ⟨rfl, rfl, rfl⟩

/-- keyAtIndexIn in three steps: the draw that batches the pairs; the sumcheck's messages; the row,
made at the summand on plain data. -/
theorem keyAtIndexIn_flat (S : Shape) (scF : Sc3) (o : Scd) (F G : Fork) (c c' : Ctx)
    (h : keyAtIndexIn S scF F c = .ok ((o, G), c')) :
    ∃ (om4 : Array E) (F1 : Fork) (c1 : Ctx) (o1 : Scd) (F2 : Fork) (c2 : Ctx),
      coinsOm S.NP F c = .ok ((om4, F1), c1) ∧
      scdIn S.scdDegrees (S.cf.lt + 1) (S.Lam + S.NP * S.cf.lt)
        (weightedSum S.NP om4 (sc3B scF)) F1 c1 = .ok ((o1, F2), c2) ∧
      scdRow o1 (keyFlat S.cf.lt S.Lam S.HA S.NP (scF.r.extract 0 S.cf.lt)
        (scF.r.extract S.cf.lt (S.cf.lt + S.cf.lgk)) (o1.r.extract 0 S.cf.lt)
        (o1.r.extract S.cf.lt (S.cf.lt + S.cf.lgk))
        (o1.r.extract (S.cf.lt + S.cf.lgk) (2 * S.cf.lt + S.cf.lgk)) om4
        (shownAt F2 o1.sEnd)) F2 c2 = .ok ((o, G), c') := by
  simp only [keyAtIndexIn] at h
  obtain ⟨om4, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨o1, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨s0, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨e1, e2, e3⟩ := foldlM_flat _
    (fun s b => addE s (keyTermFlat S.cf.lt S.Lam S.HA (shownAt F2 o1.sEnd)
      (o1.r.extract 0 S.cf.lt) (om4.getD b zeroE) b)) F2 c2
    (fun s b y G1 c4 h4 => by
      obtain ⟨t, F5, c5, h5, k5⟩ := (bind_ok _ _ _ _ _).1 h4
      obtain ⟨t1, t2, t3⟩ := keyTerm_flat S _ _ _ _ _ _ _ _ _ h5
      obtain ⟨p1, p2, p3⟩ := (pure_ok _ _ _ _ _ _).1 k5
      rw [p1, p2, p3, t1, t2, t3]
      exact ⟨rfl, rfl, rfl⟩) _ _ s0 F3 c3 h3
  rw [e1, e2, e3] at k3
  exact ⟨om4, F1, c1, o1, F2, c2, h1, h2, k3⟩

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.keyTerm_flat
#print axioms OnBytes.Tie.Pv.Att.keyAtIndexIn_flat
#print axioms OnBytes.Tie.Pv.Att.scdIn_seam
#print axioms OnBytes.Tie.Pv.Att.sc3In_seam
#print axioms OnBytes.Tie.Pv.Att.sc3Shown_flat
