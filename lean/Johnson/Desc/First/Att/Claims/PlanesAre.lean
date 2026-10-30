-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PlanesAre.lean: kind K5: what pointsOf
(Johnson/Desc/First/Att/Points.lean) lays as plane claims, member by member. PointsAre
(Johnson/Desc/First/Att/Claims/PointsRows.lean) says nothing of p.planes but a bound.

Main names:
  `foldlM_push2`: a fold that pushes one plane claim and one unit a step: both lists, member by
    member.
  `remAt g zk u s0`: the plane claim of remainder-table unit u (three planes). `remOfUnit zk u s0`:
    that of softmax-table unit u (five planes).
  `PlanesAre g zk h p`, `planes_are`: pointsOf g zk h L = some p → the remainder-table units' claims
    lie first, in the order of Geo.units .kr [.rm, .rd], each remAt … at the slot heard; unit number
    n's claim lies at k.claim = the number of remainder-table units + n and is remOfUnit zk u k.s0;
    k.below, k.pw and k.zg are the unit's.
Used of OnBytes: the field's type.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PointsRows

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard Left Pts ScoreP RemP UnitG CallG Keys)

/-- A fold that pushes one plane claim and one unit a step: both lists, member by member. -/
theorem foldlM_push2 {X : Type} (step : Array RemP × Array ScoreP → X → Option (Array RemP × Array ScoreP))
    (R : RemP → ScoreP → X → Prop)
    (hstep : ∀ acc x acc1, step acc x = some acc1 →
      ∃ rem k, acc1 = (acc.1.push rem, acc.2.push k) ∧ k.claim = acc.1.size ∧ R rem k x) :
    ∀ (xs : List X) (acc acc' : Array RemP × Array ScoreP), xs.foldlM step acc = some acc' →
      ∃ (rs : List RemP) (ks : List ScoreP), acc'.1.toList = acc.1.toList ++ rs ∧
        acc'.2.toList = acc.2.toList ++ ks ∧
        ∀ n x, xs[n]? = some x → ∃ rem k, rs[n]? = some rem ∧ ks[n]? = some k ∧
          k.claim = acc.1.size + n ∧ R rem k x
  | [], acc, acc', h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨[], [], by simp, by simp, fun n x hx => by simp at hx⟩
  | x :: xs, acc, acc', h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨acc1, h1, h2⟩ := h
    obtain ⟨rem, k, e, hc, hR⟩ := hstep acc x acc1 h1
    obtain ⟨rs, ks, e1, e2, f⟩ := foldlM_push2 step R hstep xs acc1 acc' h2
    subst e
    refine ⟨rem :: rs, k :: ks, by rw [e1]; simp, by rw [e2]; simp, fun n y hy => ?_⟩
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      exact ⟨rem, k, rfl, rfl, by rw [hc]; rfl, hR⟩
    | succ n =>
      simp only [List.getElem?_cons_succ] at hy
      obtain ⟨r', k', a1, a2, a3, a4⟩ := f n y hy
      refine ⟨r', k', a1, a2, ?_, a4⟩
      rw [a3]
      simp only [Array.size_push]
      omega

/-- The plane claim of remainder-table unit u, whose three values begin at slot s0. -/
def remAt (g : Geo) (zk : Array (Array E)) (u : ℕ × CallG × Keys) (s0 : ℕ) : RemP :=
  { call := u.1, z := P.inner (g.unitAt u.1 u.2.1 u.2.2) (zk.getD u.1 #[]), isD := u.2.2 == .rd,
    pw := P.piecesOf (g.unitAt u.1 u.2.1 u.2.2) (zk.getD u.1 #[]), s0 := s0, np := 3 }

/-- The plane claim of softmax-table unit u, whose seven values begin at slot s0. -/
def remOfUnit (zk : Array (Array E)) (u : UnitG) (s0 : ℕ) : RemP :=
  { call := u.call, z := P.inner u (zk.getD u.call #[]), isD := !u.below,
    pw := P.piecesOf u (zk.getD u.call #[]), s0 := s0, np := 5 }

/-- **What pointsOf lays as plane claims.** -/
structure PlanesAre (g : Geo) (zk : Array (Array E)) (h : Heard) (p : Pts) : Prop where
  nR : (g.units .kr [.rm, .rd]).length = h.remainders.size
  rem : ∀ (n : ℕ) (u : ℕ × CallG × Keys) (s0 : ℕ), (g.units .kr [.rm, .rd])[n]? = some u → h.remainders[n]? = some s0 →
    p.planes[n]? = some (remAt g zk u s0)
  unit : ∀ (n : ℕ) (u : UnitG) (o : ℕ × MaskedSum.Heard), g.scores[n]? = some u → h.scores[n]? = some o →
    ∃ k, p.scores[n]? = some k ∧ k.claim = h.remainders.size + n ∧
      p.planes[k.claim]? = some (remOfUnit zk u o.1) ∧ k.s0 = o.1 ∧ k.below = u.below ∧
      k.pw = P.piecesOf u (zk.getD u.call #[]) ∧ k.zg = (P.inner u (zk.getD u.call #[])).extract 0 g.lgk

theorem planes_are {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : P.pointsOf g zk h L = some p) : PlanesAre g zk h p := by
  unfold P.pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, hr, _, hn, a, hf, uW, _, uX, _, uH, _, _, hs, _, hz, e⟩ := hp
  rw [← Array.foldlM_toList] at hf
  obtain ⟨rs, ks, e1, e2, f⟩ := foldlM_push2 _
    (fun (rem : RemP) (k : ScoreP) (x : (UnitG × ℕ × MaskedSum.Heard) × Aff) =>
      rem = remOfUnit zk x.1.1 x.1.2.1 ∧ k.s0 = x.1.2.1 ∧ k.below = x.1.1.below ∧
        k.pw = P.piecesOf x.1.1 (zk.getD x.1.1.call #[]) ∧
        k.zg = (P.inner x.1.1 (zk.getD x.1.1.call #[])).extract 0 g.lgk)
    (fun acc x acc1 h1 => by
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at h1
      obtain ⟨_, _, e1⟩ := h1
      exact ⟨_, _, e1.symm, rfl, rfl, rfl, rfl, rfl, rfl⟩) _ _ _ hf
  simp only [Bool.and_eq_true, beq_iff_eq, List.size_toArray] at hr hn
  subst e
  have hsz : (((g.units .kr [.rm, .rd]).toArray.zip h.remainders).map fun (x : (ℕ × CallG × Keys) × ℕ) =>
      remAt g zk x.1 x.2).size = h.remainders.size := by
    rw [Array.size_map, Array.size_zip, List.size_toArray, hr, Nat.min_self]
  refine ⟨hr, fun n u s0 hu hs0 => ?_, fun n u o hu ho => ?_⟩
  · show a.1[n]? = _
    rw [← Array.getElem?_toList, e1]
    have hn' : n < h.remainders.size := by
      rcases Nat.lt_or_ge n h.remainders.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hs0; cases hs0
    have hz' : ((g.units .kr [.rm, .rd]).toArray.zip h.remainders)[n]? = some (u, s0) :=
      Array.getElem?_zip_eq_some.2 ⟨by rw [List.getElem?_toArray]; exact hu, hs0⟩
    rw [List.getElem?_append_left (by rw [Array.length_toList]; exact hsz ▸ hn'), Array.getElem?_toList,
      Array.getElem?_map, hz']
    rfl
  · have hL : ∃ row, L.scores[n]? = some row := by
      have hn' : n < L.scores.size := by
        rw [← hn.2]
        rcases Nat.lt_or_ge n g.scores.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at hu; cases hu
      exact ⟨_, Array.getElem?_eq_getElem hn'⟩
    obtain ⟨row, hrow⟩ := hL
    have hx : (((g.scores.toArray.zip h.scores).zip L.scores).toList)[n]? = some ((u, o), row) := by
      rw [Array.getElem?_toList]
      exact Array.getElem?_zip_eq_some.2
        ⟨Array.getElem?_zip_eq_some.2 ⟨by rw [List.getElem?_toArray]; exact hu, ho⟩, hrow⟩
    obtain ⟨rem, k, a1, a2, a3, rfl, b2, b3, b4, b5⟩ := f n _ hx
    have a3' : k.claim = h.remainders.size + n := by rw [a3]; exact congrArg (· + n) hsz
    refine ⟨k, ?_, a3', ?_, b2, b3, b4, b5⟩
    · show a.2[n]? = _
      rw [← Array.getElem?_toList, e2]
      simpa using a2
    · show a.1[k.claim]? = _
      rw [← Array.getElem?_toList, e1, a3,
        List.getElem?_append_right (by rw [Array.length_toList]; omega), Array.length_toList,
        Nat.add_sub_cancel_left]
      exact a1

end K5Law
