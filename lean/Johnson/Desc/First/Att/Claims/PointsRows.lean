-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PointsRows.lean: kind K5: what pointsOf
(Johnson/Desc/First/Att/Points.lean) lays where: the rows, the end values' first numbers, the
challenges, the calls.

Main names:
  `PointsAre g zk h L p`, `points_are`: pointsOf g zk h L = some p → PointsAre: unit by unit,
    against the zipped list of the place's units, what was heard of each and its row: sc = sumOfP
    ‹heard› ‹row›, the call, s0, pw, and claim below the number of plane claims; the sizes; the six
    other sumchecks' records; the named scalars' numbers.
  `rows_are`, `ends_are`, `chal_are`, `s0_are`, `calls_are`: the same as equations of lists.
  `scores_visited`, `units_visited`: each unit's call is a softmax-table call of the place.
  `RC K r C`: wherever the routine r returns at K, C holds. `visited_some`: where "first" returns,
    each visited unit has its tables and its plane claim.
Nothing of OnBytes is used but the types Aff and E.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.GV2

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Pts Geo Heard Left RemP ScoreP UnitG CallG)
open VerifiableInference.Desc.First.Att.P.Runs (W)
open VerifiableInference.Desc.Part

theorem guard_some {p : Prop} [Decidable p] {u : Unit} : (guard p : Option Unit) = some u ↔ p := by
  unfold guard
  split <;> simp [*]

/-- A fold that pushes one plane claim and one unit a step. -/
theorem foldlM_push {X : Type} (step : Array RemP × Array ScoreP → X → Option (Array RemP × Array ScoreP))
    (R : ScoreP → X → Prop)
    (hstep : ∀ acc x acc1, step acc x = some acc1 →
      ∃ rem k, acc1 = (acc.1.push rem, acc.2.push k) ∧ k.claim = acc.1.size ∧ R k x) :
    ∀ (xs : List X) (acc acc' : Array RemP × Array ScoreP), xs.foldlM step acc = some acc' →
      ∃ ks : List ScoreP, acc'.2.toList = acc.2.toList ++ ks ∧
        List.Forall₂ (fun k x => R k x ∧ k.claim < acc'.1.size) ks xs ∧ acc.1.size ≤ acc'.1.size
  | [], acc, acc', h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨[], by simp, .nil, le_refl _⟩
  | x :: xs, acc, acc', h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨acc1, h1, h2⟩ := h
    obtain ⟨rem, k, e, hc, hR⟩ := hstep acc x acc1 h1
    obtain ⟨ks, e2, f2, le2⟩ := foldlM_push step R hstep xs acc1 acc' h2
    subst e
    simp only [Array.size_push] at le2
    refine ⟨k :: ks, ?_, .cons ⟨hR, by omega⟩ f2, by omega⟩
    rw [e2]
    simp

/-- What pointsOf lays where. -/
structure PointsAre (g : Geo) (zk : Array (Array E)) (h : Heard) (L : Left) (p : Pts) : Prop where
  units : List.Forall₂ (fun (k : ScoreP) (x : (UnitG × ℕ × MaskedSum.Heard) × Aff) =>
      (k.sc = P.sumOfP x.1.2.2 x.2 ∧ k.call = x.1.1.call ∧ k.s0 = x.1.2.1 ∧
        k.pw = P.piecesOf x.1.1 (zk.getD x.1.1.call #[])) ∧ k.claim < p.planes.size)
    p.scores.toList ((g.scores.toArray.zip h.scores).zip L.scores).toList
  nH : g.scores.length = h.scores.size
  nL : g.scores.length = L.scores.size
  scE : p.d.scE = P.sumOfP h.division L.division
  vpm : p.d.vpm = P.sumOfP h.below L.below
  vpd : p.d.vpd = P.sumOfP h.on L.on
  scF : p.x.scF = P.sumOfP h.atIndex L.atIndex
  scd : p.x.scd = P.sumOfP h.key L.key
  scH : p.x.scH = P.sumOfP h.cells L.cells
  s5 : p.d.s5 = h.five
  sIB : p.d.sIB = h.bits
  s5h : p.d.s5h = h.two
  sCl : p.d.sCl = h.values
  sM6 : p.x.sM6 = h.maxima
  gam : p.d.gam = h.gam.getD 1 zeroE
  nW : p.d.pwW.size = g.NP

theorem points_are {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : P.pointsOf g zk h L = some p) : PointsAre g zk h L p := by
  unfold P.pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, hn, a, hf, uW, _, uX, _, uH, _, _, hs, _, _, e⟩ := hp
  rw [← Array.foldlM_toList] at hf
  obtain ⟨ks, e2, f2, _⟩ := foldlM_push _
    (fun (k : ScoreP) (x : (UnitG × ℕ × MaskedSum.Heard) × Aff) =>
      k.sc = P.sumOfP x.1.2.2 x.2 ∧ k.call = x.1.1.call ∧ k.s0 = x.1.2.1 ∧
        k.pw = P.piecesOf x.1.1 (zk.getD x.1.1.call #[]))
    (fun acc x acc1 h1 => by
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at h1
      obtain ⟨_, _, e1⟩ := h1
      exact ⟨_, _, e1.symm, rfl, rfl, rfl, rfl, rfl⟩) _ _ _ hf
  simp only [Bool.and_eq_true, beq_iff_eq, List.size_toArray] at hn hs
  subst e
  refine ⟨?_, hn.1, hn.2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hs.1.1⟩
  show List.Forall₂ _ a.2.toList _
  rw [e2]
  simpa using f2

theorem forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → f a = g b) : ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      l.map f = l'.map g
  | _, _, .nil => rfl
  | _, _, .cons h t => by rw [List.map_cons, List.map_cons, hfg _ _ h, forall₂_map_eq hfg t]

section
variable {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}

theorem zipped_snd (H : PointsAre g zk h L p) :
    ((g.scores.toArray.zip h.scores).zip L.scores).toList.map (·.2) = L.scores.toList := by
  rw [Array.toList_zip, Array.toList_zip]
  refine List.map_snd_zip ?_
  have := H.nH
  have := H.nL
  simp only [List.length_zip, Array.length_toList]
  omega

theorem zipped_mid (H : PointsAre g zk h L p) :
    ((g.scores.toArray.zip h.scores).zip L.scores).toList.map (·.1.2) = h.scores.toList := by
  rw [Array.toList_zip, Array.toList_zip]
  have h1 := H.nH
  have h2 := H.nL
  have e : ((g.scores.toArray.toList.zip h.scores.toList).zip L.scores.toList).map (·.1) =
      g.scores.toArray.toList.zip h.scores.toList := by
    refine List.map_fst_zip ?_
    simp only [List.length_zip, Array.length_toList]
    omega
  have e' : ((g.scores.toArray.toList.zip h.scores.toList).zip L.scores.toList).map (·.1.2) =
      (((g.scores.toArray.toList.zip h.scores.toList).zip L.scores.toList).map (·.1)).map (·.2) := by
    rw [List.map_map]
    rfl
  rw [e', e]
  refine List.map_snd_zip ?_
  simp only [Array.length_toList]
  omega

theorem zipped_fst (H : PointsAre g zk h L p) :
    ((g.scores.toArray.zip h.scores).zip L.scores).toList.map (·.1.1) = g.scores := by
  rw [Array.toList_zip, Array.toList_zip]
  have h1 := H.nH
  have h2 := H.nL
  have e : ((g.scores.toArray.toList.zip h.scores.toList).zip L.scores.toList).map (·.1) =
      g.scores.toArray.toList.zip h.scores.toList := by
    refine List.map_fst_zip ?_
    simp only [List.length_zip, Array.length_toList]
    omega
  have e' : ((g.scores.toArray.toList.zip h.scores.toList).zip L.scores.toList).map (·.1.1) =
      (((g.scores.toArray.toList.zip h.scores.toList).zip L.scores.toList).map (·.1)).map (·.1) := by
    rw [List.map_map]
    rfl
  rw [e', e]
  refine List.map_fst_zip ?_
  simp only [Array.length_toList]
  omega

/-- The units' rows are the rows handed in, in their order. -/
theorem rows_are (H : PointsAre g zk h L p) : p.scores.toList.map (·.sc.row) = L.scores.toList := by
  rw [← zipped_snd H]
  exact forall₂_map_eq (fun k x r => by rw [r.1.1]; rfl) H.units

/-- The units' end values begin where the hearing laid them. -/
theorem ends_are (H : PointsAre g zk h L p) :
    p.scores.toList.map (·.sc.ends) = h.scores.toList.map (·.2.sEnd) := by
  rw [← zipped_mid H, List.map_map]
  exact forall₂_map_eq (fun k x r => by rw [r.1.1]; rfl) H.units

theorem chal_are (H : PointsAre g zk h L p) :
    p.scores.toList.map (·.sc.r) = h.scores.toList.map (P.chal ·.2) := by
  rw [← zipped_mid H, List.map_map]
  exact forall₂_map_eq (fun k x r => by rw [r.1.1]; rfl) H.units

theorem s0_are (H : PointsAre g zk h L p) : p.scores.toList.map (·.s0) = h.scores.toList.map (·.1) := by
  rw [← zipped_mid H, List.map_map]
  exact forall₂_map_eq (fun k x r => r.1.2.2.1) H.units

theorem calls_are (H : PointsAre g zk h L p) : p.scores.toList.map (·.call) = g.scores.map (·.call) := by
  rw [← zipped_fst H, List.map_map]
  exact forall₂_map_eq (fun k x r => r.1.2.1) H.units

end

/-- Each softmax-table unit of the place lies in a softmax-table call of the place. -/
theorem scores_visited (g : Geo) : ∀ u ∈ g.scores,
    ∃ c, (c, u.call) ∈ g.calls.toList.zipIdx ∧ (c.tab == P.Tab.kfd) = true := by
  intro u hu
  unfold P.Geo.scores P.Geo.units at hu
  simp only [List.mem_map, List.mem_flatMap] at hu
  obtain ⟨v, ⟨x, hx, hv⟩, rfl⟩ := hu
  by_cases hc : (x.1.tab == P.Tab.kfd) = true
  · rw [if_pos hc] at hv
    simp only [List.mem_map] at hv
    obtain ⟨k, _, rfl⟩ := hv
    exact ⟨x.1, hx, hc⟩
  · rw [if_neg hc] at hv
    cases hv

theorem units_visited {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (H : PointsAre g zk h L p) : ∀ k ∈ p.scores.toList,
      ∃ c, (c, k.call) ∈ g.calls.toList.zipIdx ∧ (c.tab == P.Tab.kfd) = true := by
  intro k hk
  have : k.call ∈ p.scores.toList.map (·.call) := List.mem_map.2 ⟨k, hk, rfl⟩
  rw [calls_are H] at this
  obtain ⟨u, hu, e⟩ := List.mem_map.1 this
  rw [← e]
  exact scores_visited g u hu

/-! ### where a routine returns, a condition holds -/

variable {α β σ : Type} {K : ℕ}

/-- Wherever r returns at K, C holds. -/
def RC (K : ℕ) (r : W α) (C : Prop) : Prop := ∀ acc x, r K acc = some x → C

theorem RC.left {r : W α} {k : α → W β} {C : Prop} (h : RC K r C) : RC K (r >>= k) C := by
  intro acc x hx
  simp only [Bind.bind, ReaderT.bind, StateT.bind] at hx
  cases hr : r K acc with
  | none => simp [hr] at hx
  | some y => exact h acc y hr

theorem RC.right {r : W α} {k : α → W β} {C : Prop} (h : ∀ a, RC K (k a) C) : RC K (r >>= k) C := by
  intro acc x hx
  simp only [Bind.bind, ReaderT.bind, StateT.bind] at hx
  cases hr : r K acc with
  | none => simp [hr] at hx
  | some y =>
    simp only [hr] at hx
    exact h y.1 y.2 x hx

theorem RC.foldlM {f : σ → α → W σ} {C : Prop} {a : α} (h : ∀ s, RC K (f s a) C) :
    ∀ {xs : List α}, a ∈ xs → ∀ s, RC K (xs.foldlM f s) C
  | b :: xs, hm, s => by
    simp only [List.foldlM_cons]
    rcases List.mem_cons.1 hm with rfl | hm'
    · exact RC.left (h s)
    · exact RC.right fun s' => RC.foldlM h hm' s'

theorem RC.never {r : W α} {C : Prop} (h : ∀ acc, r K acc = none) : RC K r C := by
  intro acc x hx
  rw [h acc] at hx
  cases hx

theorem rc_unitKFD (i : P.Runs.In) (n : ℕ) (k : ScoreP) :
    RC K (P.Runs.unitKFD i n k) (∃ tb pc, i.t.score[n]? = some tb ∧ i.p.planes[k.claim]? = some pc) := by
  unfold P.Runs.unitKFD
  dsimp only
  cases h1 : i.t.score[n]? with
  | none => exact RC.left (RC.never fun _ => rfl)
  | some tb =>
    cases h2 : i.p.planes[k.claim]? with
    | none => exact RC.right fun _ => RC.left (RC.never fun _ => rfl)
    | some pc => exact fun _ _ _ => ⟨tb, pc, rfl, rfl⟩

/-- **Where "first" returns, each visited unit has its tables and its plane claim.** -/
theorem visited_some (i : P.Runs.In) (K : ℕ) (x : List Aff × P.Runs.JoinsP)
    (hr : P.Runs.firstRun i K = some x) (c : CallG) (q : ℕ) (hc : (c, q) ∈ i.g.calls.toList.zipIdx)
    (hk : (c.tab == P.Tab.kfd) = true) (k : ScoreP) (n : ℕ) (hn : (k, n) ∈ i.p.scores.toList.zipIdx)
    (hq : (k.call == q) = true) :
    ∃ tb pc, i.t.score[n]? = some tb ∧ i.p.planes[k.claim]? = some pc := by
  unfold P.Runs.firstRun P.Runs.gather at hr
  simp only [Option.map_eq_some_iff] at hr
  obtain ⟨_, ⟨y, hy, _⟩, _⟩ := hr
  refine RC.right (K := K) (fun j3 => RC.left (k := fun j => P.Runs.claim5 i j) ?_) #[] y hy
  unfold P.Runs.claim4
  refine RC.foldlM (a := (c, q)) (fun s => ?_) hc _
  rw [if_pos hk]
  refine RC.left ?_
  unfold P.Runs.callKFD
  refine RC.foldlM (a := (k, n)) (fun s => ?_) hn _
  rw [if_pos hq]
  exact RC.left (rc_unitKFD i n k)

end K5Law
