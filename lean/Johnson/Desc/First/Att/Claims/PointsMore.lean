-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PointsMore.lean: kind K5: five fields of the public records of
Johnson/Road/Rows that are no table's, paid from the return of pointsOf
(Johnson/Desc/First/Att/Points.lean) alone: ProductPub.zc, BelowPub.zi, BelowPub.wJv, ScorePub.zi
and zj; and of ScorePub.isSeg (k.seg = seg at a given seg) the disjunction: each unit's seg is fm or
fd.

Main names:
  `PointsMore g p`, `points_more`: pointsOf g zk h L = some p → the lengths that its guards give
    (zcW, ziW, each unit's zi and zj), and wJv is the tiles' sums at the value product's own
    challenges.
  `PubA h`, `pub_a`: the same in the public records' letters at h := oldOf S gL i
    (Johnson/Desc/First/Att/Claims/Any.lean).
Limit: the records' other fields that are no table's (the lengths of what was drawn; the points tied
coordinate by coordinate; "piece b is pair b"; gam) are not touched here.
Used of OnBytes: plain records; the pure functions Attention.tileSums and Model.eqTab. No routine in
a context and no theorem on a run.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PointsRows
import Johnson.Desc.First.Att.Claims.Any

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard Left Pts ScoreP RemP UnitG geoOf)

theorem size_cut' (z : Array E) {a b : ℕ} (hb : b ≤ z.size) : (z.extract a b).size = b - a := by
  rw [Array.size_extract]
  omega

theorem forall₂_left {α β : Type} {R : α → β → Prop} {Q : α → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ (fun a b => Q a ∧ R a b) l l' → ∀ a ∈ l, Q a ∧ True
  | _, _, .nil, a, h => by cases h
  | _, _, .cons h t, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact ⟨h.1, trivial⟩
    · exact forall₂_left t a ha'

/-- What more pointsOf lays: lengths that its guards give, and the tiles' sums for the value product. -/
structure PointsMore (g : Geo) (p : Pts) : Prop where
  zc : p.d.zcW.size = g.ldh
  zi : p.d.ziW.size = g.lt
  wJv : p.d.wJv = (P.tileSums g (P.eqTab (p.d.vpm.r.extract g.lgk (g.lgk + (g.lnT - 1))))
    (P.eqTab (p.d.vpm.r.extract (g.lgk + (g.lnT - 1)) (g.lgk + (g.lnT - 1) + g.lnT)))).2
  units : ∀ k ∈ p.scores.toList, k.zi.size = g.lB ∧ k.zj.size = g.lB

theorem points_more {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : P.pointsOf g zk h L = some p) : PointsMore g p := by
  unfold P.pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, hn, a, hf, uW, _, uX, _, uH, _, _, hs, _, hz, e⟩ := hp
  rw [← Array.foldlM_toList] at hf
  obtain ⟨ks, e2, f2, _⟩ := foldlM_push _
    (fun (k : ScoreP) (_ : (UnitG × ℕ × MaskedSum.Heard) × Aff) => k.zi.size = g.lB ∧ k.zj.size = g.lB)
    (fun acc x acc1 h1 => by
      simp only [Option.bind_eq_some_iff, Option.some.injEq, guard_some, beq_iff_eq] at h1
      obtain ⟨_, hg, e1⟩ := h1
      refine ⟨_, _, e1.symm, rfl, ?_, ?_⟩
      · show (Array.extract _ _ _).size = _
        rw [size_cut' _ (by omega)]
        omega
      · show (Array.extract _ _ _).size = _
        rw [size_cut' _ (by omega)]
        omega) _ _ _ hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hz
  subst e
  refine ⟨?_, ?_, rfl, ?_⟩
  · show (Array.extract _ _ _).size = _
    rw [size_cut' _ (by omega)]
    omega
  · show (Array.extract _ _ _).size = _
    rw [size_cut' _ (by omega)]
    omega
  · intro k hk
    have hk' : k ∈ a.2.toList := hk
    rw [e2] at hk'
    simp only [List.nil_append] at hk'
    exact (forall₂_left f2 k hk').1

/-! ### the same in the letters of the public records, at oldOf S gL i -/

open OnBytes.Attention

variable {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In}

/-- Five of the public records' fields that are no table's, and of isSeg the disjunction: from pointsOf's return alone. -/
structure PubA (h : Attention.Heard) : Prop where
  /-- ProductPub.zc -/
  zc : h.d.zcW.size = h.S.cf.ldh
  /-- BelowPub.zi -/
  zi : h.d.ziW.size = h.S.cf.lt
  /-- BelowPub.wJv -/
  wJv : h.d.wJv = (tileSums h.S
    (eqTab (h.d.vpm.r.extract h.S.cf.lgk (h.S.cf.lgk + (h.S.lnT - 1))))
    (eqTab (h.d.vpm.r.extract (h.S.cf.lgk + (h.S.lnT - 1))
      (h.S.cf.lgk + (h.S.lnT - 1) + h.S.lnT)))).2
  /-- ScorePub.isSeg · zi · zj -/
  units : ∀ k ∈ h.scores.toList, (k.seg = Seg.fm ∨ k.seg = Seg.fd) ∧ k.zi.size = h.S.cf.lB ∧
    k.zj.size = h.S.cf.lB

theorem pub_a (hg : i.g = geoOf S) (H : PointsMore i.g i.p) : PubA (oldOf S gL i) := by
  rw [hg] at H
  refine ⟨H.zc, H.zi, H.wJv, fun k hk => ?_⟩
  have hk' : k ∈ (i.p.scores.map scoreBack).toList := hk
  rw [Array.toList_map] at hk'
  obtain ⟨k', hm, rfl⟩ := List.mem_map.1 hk'
  refine ⟨?_, (H.units k' hm).1, (H.units k' hm).2⟩
  unfold scoreBack
  cases k'.below
  · exact .inr rfl
  · exact .inl rfl

end K5Law
