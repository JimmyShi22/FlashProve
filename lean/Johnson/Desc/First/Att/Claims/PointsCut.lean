-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PointsCut.lean: kind K5: what pointsOf
(Johnson/Desc/First/Att/Points.lean) lays into the plane claims and the softmax-table units: each
plane claim's point and pieces are those of a unit of the place; each unit's points are cuts of its
own plane claim's point, and its plane claim begins at the unit's slot and has five planes.

Main names:
  `PlaneCut g zk pc`: there is a unit with the bits of the claim's list whose inner point and pieces
    at the claim's call's key point are the claim's. `PlaneAt`: the same with the unit named: the
    pieces of the list rm | rd | fm | fd of a call of the place of the kind that holds it, with
    three planes at a remainder-table call and five at a softmax-table call.
  `UnitCut g k pc`: the unit k against its plane claim pc: slot, planes, flag, pieces, call; the
    length of the point; zg, zi, zj, zs as cuts; the tile rows' weights.
  `CutU g zk p`, `cutU_of`: pointsOf g zk h L = some p ⇒ PlaneAt at every plane claim, and at
    every unit its plane claim with UnitCut.
Used: guard_some (PointsRows.lean). No routine in a context and no theorem on a run.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PointsMore

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard Left Pts ScoreP RemP UnitG CallG Keys)

/-- A fold keeps what each of its steps keeps. -/
theorem foldlM_keeps {X A : Type} (step : A → X → Option A) (I : A → Prop) :
    ∀ (xs : List X), (∀ x ∈ xs, ∀ acc acc1, step acc x = some acc1 → I acc → I acc1) →
      ∀ acc acc' : A, xs.foldlM step acc = some acc' → I acc → I acc'
  | [], _, acc, acc', h, hi => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact h ▸ hi
  | x :: xs, hs, acc, acc', h, hi => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨acc1, h1, h2⟩ := h
    exact foldlM_keeps step I xs (fun y hy => hs y (List.mem_cons_of_mem _ hy)) acc1 acc' h2
      (hs x List.mem_cons_self acc acc1 h1 hi)

/-- A unit of the calls of one kind: its call is a call of the place, of that kind, and its list is
one of those asked for. -/
theorem units_mem (g : Geo) (t : P.Tab) (ks : List Keys) : ∀ v ∈ g.units t ks,
    (v.2.1, v.1) ∈ g.calls.toList.zipIdx ∧ (v.2.1.tab == t) = true ∧ v.2.2 ∈ ks := by
  intro v hv
  unfold P.Geo.units at hv
  simp only [List.mem_flatMap] at hv
  obtain ⟨x, hx, hv⟩ := hv
  by_cases hc : (x.1.tab == t) = true
  · rw [if_pos hc] at hv
    simp only [List.mem_map, List.mem_filter] at hv
    obtain ⟨k, ⟨hk, _⟩, rfl⟩ := hv
    exact ⟨hx, hc, hk⟩
  · rw [if_neg hc] at hv
    cases hv

theorem units_keys (g : Geo) (t : P.Tab) (ks : List Keys) : ∀ v ∈ g.units t ks, v.2.2 ∈ ks :=
  fun v hv => (units_mem g t ks v hv).2.2

/-- A plane claim's point and pieces are a unit's. -/
def PlaneCut (g : Geo) (zk : Array (Array E)) (pc : RemP) : Prop :=
  ∃ u : UnitG, u.bits = g.keyBits (if pc.isD then .rd else .rm) ∧
    pc.z = P.inner u (zk.getD pc.call #[]) ∧ pc.pw = P.piecesOf u (zk.getD pc.call #[])

/-- The same with the unit named: the claim's call c is a call of the place; the unit is that call's
pieces of the list k: rm | rd at a remainder-table call (three planes), fm | fd at a softmax-table
call (five planes), by the claim's flag. -/
def PlaneAt (g : Geo) (zk : Array (Array E)) (pc : RemP) : Prop :=
  ∃ (c : CallG) (k : Keys), (c, pc.call) ∈ g.calls.toList.zipIdx ∧
    (((c.tab == .kr) = true ∧ (k = if pc.isD then .rd else .rm) ∧ pc.np = 3) ∨
      ((c.tab == .kfd) = true ∧ (k = if pc.isD then .fd else .fm) ∧ pc.np = 5)) ∧
    pc.z = P.inner (g.unitAt pc.call c k) (zk.getD pc.call #[]) ∧
    pc.pw = P.piecesOf (g.unitAt pc.call c k) (zk.getD pc.call #[])

theorem PlaneAt.cut {g : Geo} {zk : Array (Array E)} {pc : RemP} (H : PlaneAt g zk pc) :
    PlaneCut g zk pc := by
  obtain ⟨c, k, _, hk, ez, ew⟩ := H
  refine ⟨g.unitAt pc.call c k, ?_, ez, ew⟩
  show g.keyBits k = _
  rcases hk with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
  · rfl
  · cases pc.isD <;> rfl

/-- Where the coordinates of the places in a tile begin in a unit's inner point. -/
def cutB (g : Geo) (below : Bool) : ℕ :=
  if below then g.lgk + (g.lnT - 1) + g.lnT else g.lgk + g.lnT

/-- A softmax-table unit against its plane claim. -/
structure UnitCut (g : Geo) (k : ScoreP) (pc : RemP) : Prop where
  s0 : pc.s0 = k.s0
  np : pc.np = 5
  isD : pc.isD = !k.below
  pw : pc.pw = k.pw
  call : pc.call = k.call
  size : pc.z.size = cutB g k.below + 2 * g.lB
  zg : k.zg = pc.z.extract 0 g.lgk
  zi : k.zi = pc.z.extract (cutB g k.below) (cutB g k.below + g.lB)
  zj : k.zj = pc.z.extract (cutB g k.below + g.lB) (cutB g k.below + 2 * g.lB)
  zs : k.zs = if k.below then pc.z.extract (g.lgk + (g.lnT - 1)) (cutB g k.below) else #[]
  wI : k.wI = if k.below then
      (P.tileSums g (P.eqTab (pc.z.extract g.lgk (g.lgk + (g.lnT - 1))))
        (P.eqTab (pc.z.extract (g.lgk + (g.lnT - 1)) (cutB g k.below)))).1
    else P.eqTab (pc.z.extract g.lgk (cutB g k.below))

/-- What pointsOf lays into the plane claims and the units. -/
structure CutU (g : Geo) (zk : Array (Array E)) (p : Pts) : Prop where
  planes : ∀ pc ∈ p.planes.toList, PlaneAt g zk pc
  units : ∀ k ∈ p.scores.toList, ∃ pc, p.planes[k.claim]? = some pc ∧ UnitCut g k pc

theorem score_at (g : Geo) : ∀ u ∈ g.scores, ∃ c : CallG,
    (c, u.call) ∈ g.calls.toList.zipIdx ∧ (c.tab == .kfd) = true ∧
      u = g.unitAt u.call c (if !u.below then .fd else .fm) := by
  intro u hu
  unfold P.Geo.scores at hu
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
  obtain ⟨h1, h2, hk⟩ := units_mem g _ _ v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  refine ⟨v.2.1, h1, h2, ?_⟩
  unfold P.Geo.unitAt
  rcases hk with hk | hk <;> rw [hk] <;> rfl

theorem cutU_of {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : P.pointsOf g zk h L = some p) : CutU g zk p := by
  unfold P.pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, hn, a, hf, uW, _, uX, _, uH, _, _, hs, _, hz, e⟩ := hp
  rw [← Array.foldlM_toList] at hf
  have key := foldlM_keeps _
    (fun acc : Array RemP × Array ScoreP => (∀ pc ∈ acc.1.toList, PlaneAt g zk pc) ∧
      ∀ k ∈ acc.2.toList, ∃ pc, acc.1[k.claim]? = some pc ∧ UnitCut g k pc) _
    (fun x hx acc acc1 h1 hI => by
      have hu : x.1.1 ∈ g.scores := by
        rw [Array.toList_zip, Array.toList_zip] at hx
        have := (List.of_mem_zip (a := x.1) (b := x.2) hx).1
        have := (List.of_mem_zip (a := x.1.1) (b := x.1.2) this).1
        simpa using this
      simp only [Option.bind_eq_some_iff, Option.some.injEq, guard_some, beq_iff_eq] at h1
      obtain ⟨_, hg, e1⟩ := h1
      subst e1
      refine ⟨?_, ?_⟩
      · intro pc hpc
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hpc
        rcases hpc with hpc | rfl
        · exact hI.1 pc hpc
        · obtain ⟨c, h1, h2, h3⟩ := score_at g _ hu
          refine ⟨c, _, h1, .inr ⟨h2, rfl, rfl⟩, ?_, ?_⟩
          · show P.inner x.1.1 _ = P.inner (g.unitAt x.1.1.call c _) _
            rw [← h3]
          · show P.piecesOf x.1.1 _ = P.piecesOf (g.unitAt x.1.1.call c _) _
            rw [← h3]
      · intro k hk
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hk
        rcases hk with hk | rfl
        · obtain ⟨pc, e2, U⟩ := hI.2 k hk
          refine ⟨pc, ?_, U⟩
          have hlt : k.claim < acc.1.size := by
            by_contra hc
            rw [Array.getElem?_eq_none (by omega)] at e2
            cases e2
          rw [Array.getElem?_push, if_neg (by omega)]
          exact e2
        · refine ⟨_, Array.getElem?_push_size, ?_⟩
          refine ⟨rfl, rfl, rfl, rfl, rfl, hg, rfl, rfl, rfl, ?_, ?_⟩
          · dsimp only
            cases x.1.1.below <;> simp only [cutB, Bool.false_eq_true, if_false, if_true]
          · dsimp only
            cases x.1.1.below <;> simp only [cutB, Bool.false_eq_true, if_false, if_true]) _ _ hf ?_
  · subst e
    exact ⟨key.1, key.2⟩
  · refine ⟨?_, fun k hk => by simp at hk⟩
    intro pc hpc
    simp only [Array.toList_map, Array.toList_zip, List.mem_map] at hpc
    obtain ⟨y, hy, rfl⟩ := hpc
    have hu : y.1 ∈ g.units .kr [.rm, .rd] := by
      have := (List.of_mem_zip (a := y.1) (b := y.2) hy).1
      simpa using this
    obtain ⟨h1, h2, hk⟩ := units_mem g _ _ y.1 hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    refine ⟨y.1.2.1, y.1.2.2, h1, .inl ⟨h2, ?_, rfl⟩, rfl, rfl⟩
    rcases hk with hk | hk <;> rw [hk] <;> rfl

end K5Law

#print axioms K5Law.cutU_of
