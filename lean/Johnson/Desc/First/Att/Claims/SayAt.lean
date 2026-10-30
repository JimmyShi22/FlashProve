-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/SayAt.lean: kind K5: what the claims say at a record i of the kind's
own whose points are pointsOf's (`PointsAre`, Johnson/Desc/First/Att/Claims/PointsRows.lean) and at
which "first" and "second" return.

Main names:
  `tbBack`: a unit's tables as the record of OnBytes/Model. `unitReader`: the reader's form under
    end value number j of unit number n.
  `Visited`, `say4_units`: where each unit's call is a softmax-table call, claim 4 speaks of every
    unit, not of the visited alone.
  `SayAt`: the remainder-table units' plane values; every unit n has its tables tb and its plane
    claim pc, and UnitAt holds (planes, maximum, the row worth 0, the end values j < 2 · pieces);
    Say5 … Say8.
  `Spec.SayAtIff`, `say_at`: AllZero ρ W (l₁ ++ l₂) ↔ SayAt.
  `unit_at`, `tail_rows`, `tail_ends`: the same in the hearing's names: the n-th row handed to
    pointsOf is worth 0; the slot (the n-th heard sumcheck's sEnd + j) is worth the reader's form;
    L.division, below, on, atIndex, key, cells are worth 0.
Premises, all named: i.g = geoOf S; i.zk = gL.zk; A.NC = S.calls.size; PointsAre i.g zk h L i.p
(paid by points_are wherever i.p is pointsOf's); the two runs' return.
Limit: oldOf feeds the written lists alone here: no statement of OnBytes on what a sumcheck's state
is worth is used or usable at it; the rows are the kind's own.
Used of OnBytes: as Johnson/Desc/First/Att/Claims/Say.lean and
Johnson/Desc/First/Att/Claims/Any.lean.
Not claimed: that a claim holds; what an entry of a table means for a message.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Say58
import Johnson.Desc.First.Att.Claims.PointsRows

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Pts TablesP ScoreT ScoreP RemP geoOf callOf tabOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP)

variable {Kf : Type} [CommRing Kf] (ρ : Reading Kf) (W : World Kf)

def tbBack (s : ScoreT) : ScoreTables := { tM := s.tM, tQ := s.tQ, tK := s.tK }

variable (S : Shape) (gL : Forest.Heard) (i : P.Runs.In) (K : ℕ)

theorem old_score (n : ℕ) : (oldOf S gL i).t.score[n]? = (i.t.score[n]?).map tbBack := by
  show (i.t.score.map _)[n]? = _
  rw [Array.getElem?_map]
  rfl

theorem old_plane (n : ℕ) : (oldOf S gL i).planes[n]? = (i.p.planes[n]?).map remBack := by
  show (i.p.planes.map _)[n]? = _
  rw [Array.getElem?_map]

theorem old_scores_zip :
    (oldOf S gL i).scores.toList.zipIdx = i.p.scores.toList.zipIdx.map fun x => (scoreBack x.1, x.2) := by
  show (i.p.scores.map scoreBack).toList.zipIdx = _
  rw [Array.toList_map, List.zipIdx_map]
  rfl

/-- What the claims say at a record of the kind's own. -/
structure SayAt : Prop where
  s3 : Say3 ρ W (oldOf S gL i) K
  units : ∀ x ∈ i.p.scores.toList.zipIdx, ∃ tb pc, i.t.score[x.2]? = some tb ∧
    i.p.planes[x.1.claim]? = some pc ∧
      UnitAt ρ W (oldOf S gL i) K (scoreBack x.1) (tbBack tb) (remBack pc)
  s5 : Say5 ρ W (oldOf S gL i) K
  s6 : Say6 ρ W (oldOf S gL i) K
  s7 : Say7 ρ W (oldOf S gL i) K
  s8 : Say8 ρ W (oldOf S gL i) K

/-- Each unit's call is a softmax-table call of the place. -/
def Visited : Prop :=
  ∀ k ∈ i.p.scores.toList, ∃ c, (c, k.call) ∈ i.g.calls.toList.zipIdx ∧ (c.tab == P.Tab.kfd) = true

variable {S gL i K}

theorem say4_units (hg : i.g = geoOf S) (hv : Visited i)
    (hs : ∀ x ∈ i.p.scores.toList.zipIdx, ∃ tb pc, i.t.score[x.2]? = some tb ∧
      i.p.planes[x.1.claim]? = some pc) :
    Say4 ρ W (oldOf S gL i) K ↔ ∀ x ∈ i.p.scores.toList.zipIdx, ∃ tb pc, i.t.score[x.2]? = some tb ∧
      i.p.planes[x.1.claim]? = some pc ∧
        UnitAt ρ W (oldOf S gL i) K (scoreBack x.1) (tbBack tb) (remBack pc) := by
  unfold Say4 UnitSay
  rw [old_scores_zip]
  constructor
  · intro H x hx
    obtain ⟨tb, pc, h1, h2⟩ := hs x hx
    refine ⟨tb, pc, h1, h2, ?_⟩
    obtain ⟨c', hc', ht⟩ := hv x.1 (List.mem_zipIdx_iff_getElem?.1 hx |> fun e => List.mem_of_getElem? e)
    rw [hg, calls_zip] at hc'
    obtain ⟨y, hy, e⟩ := List.mem_map.1 hc'
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    refine H y hy ?_ (scoreBack x.1, x.2) (List.mem_map.2 ⟨x, hx, rfl⟩) ?_ _ _ ?_ ?_
    · rw [← tab_eq y.1.kind Table.kfd]
      rw [← e1] at ht
      exact ht
    · show (x.1.call == y.2) = true
      rw [e2]
      exact beq_self_eq_true _
    · rw [old_score, h1]
      rfl
    · show (oldOf S gL i).planes[x.1.claim]? = _
      rw [old_plane, h2]
      rfl
  · intro H y _ _ z hz _ tb' pc' h1 h2
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    obtain ⟨tb, pc, g1, g2, U⟩ := H x hx
    rw [old_score, g1] at h1
    have h2' : (oldOf S gL i).planes[x.1.claim]? = some pc' := h2
    rw [old_plane, g2] at h2'
    rw [← Option.some.inj h1, ← Option.some.inj h2']
    exact U

namespace Spec

def SayAtIff : Prop :=
  ∀ (Kf : Type) [CommRing Kf] (ρ : Reading Kf) (W : World Kf) (A : Plan) (S : Shape)
    (gL : Forest.Heard) (i : P.Runs.In) (K : ℕ) (l₁ l₂ : List Aff) (j : JoinsP),
    i.g = geoOf S → i.zk = gL.zk → A.NC = S.calls.size → Visited i →
    P.Runs.firstRun i K = some (l₁, j) → P.Runs.secondRun i K = some l₂ →
      (AllZero ρ W (l₁ ++ l₂) ↔ SayAt ρ W S gL i K)

end Spec

theorem say_at : Spec.SayAtIff := by
  intro Kf _ ρ W A S gL i K l₁ l₂ j hg hz hN hv h1 h2
  rw [say_iff Kf ρ W A S gL i K l₁ l₂ j hg hz hN h1 h2]
  have hs : ∀ x ∈ i.p.scores.toList.zipIdx, ∃ tb pc, i.t.score[x.2]? = some tb ∧
      i.p.planes[x.1.claim]? = some pc := by
    intro x hx
    obtain ⟨c, hc, ht⟩ := hv x.1 (List.mem_zipIdx_iff_getElem?.1 hx |> fun e => List.mem_of_getElem? e)
    exact visited_some i K _ h1 c x.1.call hc ht x.1 x.2 hx (beq_self_eq_true _)
  constructor
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, (say4_units ρ W hg hv hs).1 b, c, d, e, f⟩
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, (say4_units ρ W hg hv hs).2 b, c, d, e, f⟩

/-! ### in the hearing's own names -/

section
variable {Kf : Type} [CommRing Kf] {ρ : Reading Kf} {W : World Kf} {S : Shape} {gL : Forest.Heard}
  {i : P.Runs.In} {K : ℕ} {zk : Array (Array E)} {h : P.Heard} {L : P.Left}

/-- The reader's form under end value number j of unit number n. -/
def unitReader (S : Shape) (gL : Forest.Heard) (i : P.Runs.In) (K n j : ℕ) : Aff :=
  match i.p.scores[n]?, i.t.score[n]? with
  | some k, some tb => endsU (oldOf S gL i) K (scoreBack k) (tbBack tb) j
  | _, _ => {}

/-- The six rows behind the units, as they were handed to pointsOf, are worth 0. -/
theorem tail_rows (H : PointsAre i.g zk h L i.p) (Sy : SayAt ρ W S gL i K) :
    L.division.value ρ W = 0 ∧ L.below.value ρ W = 0 ∧ L.on.value ρ W = 0 ∧
      L.atIndex.value ρ W = 0 ∧ L.key.value ρ W = 0 ∧ L.cells.value ρ W = 0 := by
  have a : i.p.d.scE.row.value ρ W = 0 := Sy.s5.row
  have b : i.p.d.vpm.row.value ρ W = 0 := Sy.s6.below.row
  have c : i.p.d.vpd.row.value ρ W = 0 := Sy.s6.on.row
  have d : i.p.x.scF.row.value ρ W = 0 := Sy.s7.rowF
  have e : i.p.x.scd.row.value ρ W = 0 := Sy.s7.rowK
  have f : i.p.x.scH.row.value ρ W = 0 := Sy.s8.row
  rw [H.scE] at a
  rw [H.vpm] at b
  rw [H.vpd] at c
  rw [H.scF] at d
  rw [H.scd] at e
  rw [H.scH] at f
  exact ⟨a, b, c, d, e, f⟩

/-- The end values behind the units: each slot's worth is its reader's form's. -/
theorem tail_ends (H : PointsAre i.g zk h L i.p) (Sy : SayAt ρ W S gL i K) :
    (∀ j < 2 * S.NP, W.slot (h.division.sEnd + j) = (endsE (oldOf S gL i) K j).value ρ W) ∧
    (∀ j < 2 * S.NP, W.slot (h.below.sEnd + j) = (endsV (oldOf S gL i) K (sum3Back i.p.d.vpm) i.t.tVM
      i.t.ptM false i.t.qVM j).value ρ W) ∧
    (∀ j < 2 * S.NP, W.slot (h.on.sEnd + j) = (endsV (oldOf S gL i) K (sum3Back i.p.d.vpd) i.t.tVD
      i.t.ptD true i.t.qVD j).value ρ W) ∧
    (∀ b < S.NP, W.slot (h.atIndex.sEnd + 2 * b) = (Fo.readHeadT (oldOf S gL i) K i.t.qF S.atQ
      ((oldOf S gL i).x.rg S) ((oldOf S gL i).x.rc S) (b / S.HA) (b % S.HA)).value ρ W) ∧
    (∀ j < S.Lam + S.NP * S.cf.lt, W.slot (h.key.sEnd + j) = (endsK (oldOf S gL i) K j).value ρ W) ∧
    (∀ j < 2 * S.NP, W.slot (h.cells.sEnd + j) = (endsH (oldOf S gL i) K j).value ρ W) := by
  have a : ∀ j < 2 * S.NP, W.slot (i.p.d.scE.ends + j) = _ := Sy.s5.ends
  have b : ∀ j < 2 * S.NP, W.slot (i.p.d.vpm.ends + j) = _ := Sy.s6.below.ends
  have c : ∀ j < 2 * S.NP, W.slot (i.p.d.vpd.ends + j) = _ := Sy.s6.on.ends
  have d : ∀ b < S.NP, W.slot (i.p.x.scF.ends + 2 * b) = _ := Sy.s7.endsF
  have e : ∀ j < S.Lam + S.NP * S.cf.lt, W.slot (i.p.x.scd.ends + j) = _ := Sy.s7.endsK
  have f : ∀ j < 2 * S.NP, W.slot (i.p.x.scH.ends + j) = _ := Sy.s8.ends
  rw [H.scE] at a
  rw [H.vpm] at b
  rw [H.vpd] at c
  rw [H.scF] at d
  rw [H.scd] at e
  rw [H.scH] at f
  exact ⟨a, b, c, d, e, f⟩

/-- **Unit number n, in the hearing's names**: its row, as handed to pointsOf, is worth 0; each of its end values' slots is worth its reader's form. -/
theorem unit_at (H : PointsAre i.g zk h L i.p) (Sy : SayAt ρ W S gL i K) (n : ℕ)
    (o : ℕ × VerifiableInference.Desc.Part.MaskedSum.Heard) (ho : h.scores[n]? = some o) :
    ∃ k f, i.p.scores[n]? = some k ∧ L.scores[n]? = some f ∧ k.sc = P.sumOfP o.2 f ∧ k.s0 = o.1 ∧
      f.value ρ W = 0 ∧
      ∀ j < 2 * k.pw.size, W.slot (o.2.sEnd + j) = (unitReader S gL i K n j).value ρ W := by
  have e1 := congrArg (·[n]?) (ends_are H)
  have e2 := congrArg (·[n]?) (rows_are H)
  have e3 := congrArg (·[n]?) (chal_are H)
  have e4 := congrArg (·[n]?) (s0_are H)
  simp only [List.getElem?_map, Array.getElem?_toList, ho, Option.map_some] at e1 e2 e3 e4
  cases hk : i.p.scores[n]? with
  | none => rw [hk] at e1; cases e1
  | some k =>
    rw [hk] at e1 e2 e3 e4
    simp only [Option.map_some, Option.some.injEq] at e1 e3 e4
    have hx : (k, n) ∈ i.p.scores.toList.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]
      simpa using hk
    obtain ⟨tb, pc, h1, _, U⟩ := Sy.units (k, n) hx
    refine ⟨k, k.sc.row, rfl, e2.symm, ?_, e4, U.row, ?_⟩
    · show k.sc = { r := P.chal o.2, ends := o.2.sEnd, row := k.sc.row }
      rw [← e1, ← e3]
    · intro j hj
      have hsz : (scoreBack k).pw.size = k.pw.size := by
        show (k.pw.map _).size = _
        rw [Array.size_map]
      have := U.ends j (by rw [hsz]; exact hj)
      unfold unitReader
      rw [hk, h1, ← e1]
      exact this

end

end K5Law
