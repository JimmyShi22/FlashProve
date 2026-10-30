-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Place.lean: kind K5: the place's four calls: one public record in the
place of four premises.

Main names:
  `PlaceIs S c0 c1 c2 c3`: the shape's calls are these four; their kinds of table are kr, kfd, r16,
    wh; the lists that they hold are [rm, rd], [fm, fd], [wl, ix], [wh]. A test on the shape decides
    it.
  `place_zip`; `place_kr`: Geo.units .kr [.rm, .rd] is the two remainder-table units of call 0;
    `place_scores`: Geo.scores is the two softmax-table units of call 1, the one below the diagonal
    first; `place_wh`: the unit of the list wh lies in call 3.
  `points_counts`: more of what pointsOf lays: d.qWH is the call of the unit of the list wh; how
    many plane claims and units there are.
  `list_two`, `list_four`; `sixPl i zk c0 c1 a1 a2 k1 k2`: the six
    (Johnson/Desc/First/Att/Claims/PortAll.lean) at such a place; `callsAre_of`: CallsAre
    (Johnson/Desc/First/Att/Claims/PortJoin.lean), from PlaceIs and the return of pointsOf.
Limit: PlaceIs is a premise. It is the call list of UsualCalls (Johnson/Road/Lane5AttLaid.lean) as
it lies in the shape; that shapeHid at such a call list gives it is not shown in this file or in
what it imports. No test of the verifier asks it.
Used of OnBytes: plain records (Shape, ACall, Seg, Table).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PortMine
import Johnson.Desc.First.Att.Claims.PortJoin

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo CallG Keys UnitG ScoreP RemP Heard Left Pts geoOf callOf keysOf tabOf)

/-- **The place's four calls**: their kinds of table and the lists of keys that each holds. Public facts on the plan: a test on the shape decides them. -/
structure PlaceIs (S : Attention.Shape) (c0 c1 c2 c3 : ACall) : Prop where
  calls : S.calls.toList = [c0, c1, c2, c3]
  k0 : c0.kind = .kr
  k1 : c1.kind = .kfd
  k2 : c2.kind = .r16
  k3 : c3.kind = .wh
  g0 : c0.segs = [.rm, .rd]
  g1 : c1.segs = [.fm, .fd]
  g2 : c2.segs = [.wl, .ix]
  g3 : c3.segs = [.wh]

variable {S : Attention.Shape} {c0 c1 c2 c3 : ACall}

theorem place_zip (Pl : PlaceIs S c0 c1 c2 c3) : (geoOf S).calls.toList.zipIdx =
    [(callOf c0, 0), (callOf c1, 1), (callOf c2, 2), (callOf c3, 3)] := by
  rw [calls_zip, Pl.calls]
  rfl

/-- The two remainder-table units. -/
theorem place_kr (Pl : PlaceIs S c0 c1 c2 c3) : (geoOf S).units .kr [.rm, .rd] =
    [(0, callOf c0, .rm), (0, callOf c0, .rd)] := by
  unfold P.Geo.units
  rw [place_zip Pl]
  simp [callOf, tabOf, P.CallG.holds, keysOf, Pl.k0, Pl.k1, Pl.k2, Pl.k3, Pl.g0]

/-- The two softmax-table units: the one below the diagonal first. -/
theorem place_scores (Pl : PlaceIs S c0 c1 c2 c3) : (geoOf S).scores =
    [(geoOf S).unitAt 1 (callOf c1) .fm, (geoOf S).unitAt 1 (callOf c1) .fd] := by
  unfold P.Geo.scores P.Geo.units
  rw [place_zip Pl]
  simp [callOf, tabOf, P.CallG.holds, keysOf, Pl.k0, Pl.k1, Pl.k2, Pl.k3, Pl.g1]

/-- The unit of the list wh lies in call 3. -/
theorem place_wh (Pl : PlaceIs S c0 c1 c2 c3) :
    (geoOf S).single .wh = some ((geoOf S).unitAt 3 (callOf c3) .wh) := by
  have e3 : (geoOf S).calls[3]? = some (callOf c3) := by
    have : (geoOf S).calls.toList = [callOf c0, callOf c1, callOf c2, callOf c3] := by
      show (S.calls.map callOf).toList = _
      rw [Array.toList_map, Pl.calls]
      rfl
    rw [← Array.getElem?_toList, this]
    rfl
  unfold P.Geo.single P.Geo.lastHolding
  rw [place_zip Pl]
  simp [callOf, P.CallG.holds, keysOf, Pl.g0, Pl.g1, Pl.g2, Pl.g3, e3]

/-- More of what pointsOf lays: the call of the list wh, and how many plane claims and units there are. -/
theorem points_counts {g : Geo} {zk : Array (Array E)} {h : P.Heard} {L : Left} {p : Pts}
    (hp : P.pointsOf g zk h L = some p) :
    (∃ uH, g.single .wh = some uH ∧ p.d.qWH = uH.call) ∧
      p.planes.size = h.remainders.size + h.scores.size ∧ p.scores.size = h.scores.size := by
  unfold P.pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, hr, _, hn, a, hf, uW, _, uX, _, uH, hH, _, hs, _, hz, e⟩ := hp
  rw [← Array.foldlM_toList] at hf
  have key : ∀ (xs : List ((UnitG × ℕ × MaskedSum.Heard) × Aff)) (acc acc' : Array RemP × Array ScoreP)
      (step : Array RemP × Array ScoreP → (UnitG × ℕ × MaskedSum.Heard) × Aff →
        Option (Array RemP × Array ScoreP)),
      (∀ acc x acc1, step acc x = some acc1 → acc1.1.size = acc.1.size + 1 ∧ acc1.2.size = acc.2.size + 1) →
      xs.foldlM step acc = some acc' →
      acc'.1.size = acc.1.size + xs.length ∧ acc'.2.size = acc.2.size + xs.length := by
    intro xs
    induction xs with
    | nil =>
      intro acc acc' step _ h0
      simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h0
      subst h0
      exact ⟨rfl, rfl⟩
    | cons x xs ih =>
      intro acc acc' step hst h0
      simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h0
      obtain ⟨acc1, h1, h2⟩ := h0
      obtain ⟨s1, s2⟩ := hst acc x acc1 h1
      obtain ⟨t1, t2⟩ := ih acc1 acc' step hst h2
      rw [List.length_cons]
      omega
  obtain ⟨z1, z2⟩ := key _ _ _ _ (fun acc x acc1 h1 => by
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h1
    obtain ⟨_, _, e1⟩ := h1
    rw [← e1]
    simp) hf
  simp only [Bool.and_eq_true, beq_iff_eq, List.size_toArray] at hr hn
  subst e
  have hl : (((g.scores.toArray.zip h.scores).zip L.scores).toList).length = h.scores.size := by
    rw [Array.length_toList, Array.size_zip, Array.size_zip, List.size_toArray, ← hn.2, hn.1]
    simp
  refine ⟨⟨uH, hH, rfl⟩, ?_, ?_⟩
  · show a.1.size = _
    rw [z1, hl, Array.size_map, Array.size_zip, List.size_toArray, hr, Nat.min_self]
  · show a.2.size = _
    rw [z2, hl]
    simp

theorem list_two {α : Type} {l : List α} {a b : α} (hn : l.length = 2) (h0 : l[0]? = some a)
    (h1 : l[1]? = some b) : l = [a, b] := by
  match l, hn with
  | [x, y], _ =>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
    rw [h0, h1]

theorem list_four {α : Type} {l : List α} {a b c d : α} (hn : l.length = 4) (h0 : l[0]? = some a)
    (h1 : l[1]? = some b) (h2 : l[2]? = some c) (h3 : l[3]? = some d) : l = [a, b, c, d] := by
  match l, hn with
  | [x, y, z, w], _ =>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1 h2 h3
    rw [h0, h1, h2, h3]

variable {gL : Forest.Heard} {i : P.Runs.In}

/-- The six at a place with these four calls. -/
def sixPl (i : P.Runs.In) (zk : Array (Array E)) (c0 c1 : ACall) (a1 a2 : ℕ) (k1 k2 : ScoreP) : Six :=
  sixAt i.g zk (0, callOf c0, .rm) (0, callOf c0, .rd) a1 a2 k1 k2 (i.g.unitAt 1 (callOf c1) .fm)
    (i.g.unitAt 1 (callOf c1) .fd)

/-- **CallsAre, paid**: from the place's four calls and the return of pointsOf. -/
theorem callsAre_of (Pl : PlaceIs S c0 c1 c2 c3) (hg : i.g = geoOf S) {zk : Array (Array E)} {hh : P.Heard}
    {L : Left} (hP : P.pointsOf i.g zk hh L = some i.p) {a1 a2 : ℕ} {k1 k2 : ScoreP}
    (ha1 : hh.remainders[0]? = some a1) (ha2 : hh.remainders[1]? = some a2)
    (hk1 : i.p.scores[0]? = some k1) (hk2 : i.p.scores[1]? = some k2) :
    CallsAre (oldOf S gL i) (sixPl i zk c0 c1 a1 a2 k1 k2) c0 c1 c2 c3 := by
  have PA := points_are hP
  have Pn := planes_are hP
  obtain ⟨⟨uH, hH, eH⟩, nP, nS⟩ := points_counts hP
  have hkr : i.g.units .kr [.rm, .rd] = [(0, callOf c0, .rm), (0, callOf c0, .rd)] := by
    rw [hg]; exact place_kr Pl
  have hgs : i.g.scores = [i.g.unitAt 1 (callOf c1) .fm, i.g.unitAt 1 (callOf c1) .fd] := by
    rw [hg]; exact place_scores Pl
  have nR : hh.remainders.size = 2 := by rw [← Pn.nR, hkr]; rfl
  have nH : hh.scores.size = 2 := by rw [← PA.nH, hgs]; rfl
  have eo1 : hh.scores[0]? = some hh.scores[0] := Array.getElem?_eq_getElem (by omega)
  have eo2 : hh.scores[1]? = some hh.scores[1] := Array.getElem?_eq_getElem (by omega)
  have p1 := Pn.rem 0 _ _ (by rw [hkr]; rfl) ha1
  have p2 := Pn.rem 1 _ _ (by rw [hkr]; rfl) ha2
  obtain ⟨k1', s1, q1, d1, z1, _, _, _⟩ := Pn.unit 0 _ _ (by rw [hgs]; rfl) eo1
  obtain ⟨k2', s2, q2, d2, z2, _, _, _⟩ := Pn.unit 1 _ _ (by rw [hgs]; rfl) eo2
  rw [hk1] at s1
  rw [hk2] at s2
  have e1 : k1' = k1 := (Option.some.inj s1).symm
  have e2 : k2' = k2 := (Option.some.inj s2).symm
  subst e1 e2
  rw [← z1, q1, nR] at d1
  rw [← z2, q2, nR] at d2
  have lp : i.p.planes.toList = [remAt i.g zk (0, callOf c0, .rm) a1, remAt i.g zk (0, callOf c0, .rd) a2,
      remOfUnit zk (i.g.unitAt 1 (callOf c1) .fm) k1'.s0,
      remOfUnit zk (i.g.unitAt 1 (callOf c1) .fd) k2'.s0] :=
    list_four (by rw [Array.length_toList, nP, nR, nH]) (by rw [Array.getElem?_toList]; exact p1)
      (by rw [Array.getElem?_toList]; exact p2) (by rw [Array.getElem?_toList]; exact d1)
      (by rw [Array.getElem?_toList]; exact d2)
  have ls : i.p.scores.toList = [k1', k2'] :=
    list_two (by rw [Array.length_toList, nS, nH]) (by rw [Array.getElem?_toList]; exact hk1)
      (by rw [Array.getElem?_toList]; exact hk2)
  have cc := calls_are PA
  rw [ls, hgs] at cc
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at cc
  have hH' : uH = (geoOf S).unitAt 3 (callOf c3) .wh := by
    rw [hg, place_wh Pl] at hH
    exact (Option.some.inj hH).symm
  refine ⟨Pl.calls, Pl.k0, Pl.k1, Pl.k2, Pl.k3, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_, cc.1, cc.2⟩
  · unfold ACall.holds; rw [Pl.g2]; rfl
  · unfold ACall.holds; rw [Pl.g2]; rfl
  · show i.p.d.qWH = 3
    rw [eH, hH']
    rfl
  · show (i.p.planes.map remBack).toList = _
    rw [Array.toList_map, lp]
    rfl
  · show (i.p.scores.map scoreBack).toList = _
    rw [Array.toList_map, ls]
    rfl

end K5Law
