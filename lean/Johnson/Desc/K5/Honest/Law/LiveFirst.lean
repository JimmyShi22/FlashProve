-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/LiveFirst.lean: CONDITIONAL: an attention segment's own rounds: every
slot from the first up to the two value products' scalars, but the accumulator's, is named by a form
of the run "first" with a coefficient that does not read 0, where the test on the drawn elements
says yes. Statements with their proofs ON THE VERIFIER'S OWN DATA: no prover is in this file.

Main names:
  units_mem, visited_of   a unit's call is a call of its kind of table
  fold_planes, planes_spec   what the verifier's function of the points lays into its list of plane
                  claims: the remainder units' in front, by number; each softmax-table unit's at
                  the number that the unit holds
  forall2_left, forall2_right   two lists in a relation, member by member, by number
  planes_region, units_region   a slot in the plan's stretch of the remainder units, of the
                  softmax-table units, lies in one unit's stretch
  rem_mem, unit_mem   a remainder unit's list, a softmax-table unit's list, lies in the run's
  k5_live_first   **the statement**

k5_live_first is CONDITIONAL. The premises, and who is meant to show each:
  hh, li, hp, h1: the hearing, the rows, the points and the run return; hz: the hearing starts from
    a ledger whose arrays have their length: whoever has the block's yes.
  gf, hg, hzk, hN: public (hN and the plan A are asked by first_any,
    Johnson/Desc/First/Att/Claims/Any.lean, and read nowhere else). gf (LiveFits,
    Johnson/Desc/K5/Honest/Law/LiveSecond.lean) has a clause that is truly needed: unit by unit, a
    softmax-table unit's sumcheck has two end values for each of the unit's PIECES. The run names
    the end values of a unit's pieces alone: were there more end values than that, the slots
    beyond would be named by no form of either run, whatever is drawn.
  hL: the test on the drawn elements (heardLive, Johnson/Desc/K5/Honest/Law/Live.lean) says yes.
Three kinds of slots are named by the run inside a row's claimed sum alone: a unit's seventh scalar
and the second of the five scalars here, the second end values of the score at the index in the run
"second". For these the element that scales the claimed sum must not read 0 either.
Limits. It speaks of the forms that the run gathers, not of claims in a state's list. The key forms,
which name some of these slots too, lie in no list of this run.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.LiveSecond

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc.Part (MaskedSum.Heard)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)
open VerifiableInference.Desc.First.Att.P (Geo geoOf callOf tabOf Heard Left Pts RemP ScoreP UnitG
  CallG Tab Keys hear pointsOf LeftIs formOf own3 kB kE kV numsOf numsPlan Nums planesPlan
  unitsPlan unitsNext piecesOf_size inner piecesOf)
open VerifiableInference.Desc.First.Att.P.Runs (In JoinsP firstRun)
open K5Law (PointsAre points_are oldOf first_any Visited visited_some remBack scoreBack tbBack
  calls_zip tab_eq old_score old_plane old_scores_zip guard_some)

/-! ## 1 Units and their calls -/

/-- A unit of a kind of table stands at a call of that kind. -/
theorem units_mem {g : Geo} {t : Tab} {ks : List Keys} {u : ℕ × CallG × Keys}
    (h : u ∈ g.units t ks) : (u.2.1, u.1) ∈ g.calls.toList.zipIdx ∧ (u.2.1.tab == t) = true := by
  unfold Geo.units at h
  obtain ⟨y, hy, hu⟩ := List.mem_flatMap.1 h
  by_cases c : (y.1.tab == t) = true
  · rw [if_pos c] at hu
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hu
    exact ⟨hy, c⟩
  · rw [if_neg c] at hu
    exact nomatch hu

theorem forall2_left {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → ∀ (m : ℕ) (a : α), l[m]? = some a → ∃ b, l'[m]? = some b ∧ R a b
  | _, _, .nil, _, _, h => nomatch h
  | _, _, .cons hp _, 0, a, h => by
    rw [List.getElem?_cons_zero] at h
    exact ⟨_, List.getElem?_cons_zero, Option.some.inj h ▸ hp⟩
  | _, _, .cons _ ht, m + 1, a, h => by
    rw [List.getElem?_cons_succ] at h
    obtain ⟨b, hb, hr⟩ := forall2_left ht m a h
    exact ⟨b, by rw [List.getElem?_cons_succ]; exact hb, hr⟩

theorem forall2_right {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → ∀ (m : ℕ) (b : β), l'[m]? = some b → ∃ a, l[m]? = some a ∧ R a b
  | _, _, .nil, _, _, h => nomatch h
  | _, _, .cons hp _, 0, b, h => by
    rw [List.getElem?_cons_zero] at h
    exact ⟨_, List.getElem?_cons_zero, Option.some.inj h ▸ hp⟩
  | _, _, .cons _ ht, m + 1, b, h => by
    rw [List.getElem?_cons_succ] at h
    obtain ⟨a, ha, hr⟩ := forall2_right ht m b h
    exact ⟨a, by rw [List.getElem?_cons_succ]; exact ha, hr⟩

/-- **Each softmax-table unit's call is a softmax-table call of the place.** -/
theorem visited_of {i : In} {zk : Array (Array E)} {h : Heard} {L : Left}
    (PA : PointsAre i.g zk h L i.p) : Visited i := by
  intro k hk
  obtain ⟨m, hm, e⟩ := List.getElem_of_mem hk
  obtain ⟨z, hz, ⟨_, hc, _, _⟩, _⟩ := forall2_left PA.units m k
    (by rw [List.getElem?_eq_getElem hm, e])
  have h1 := List.mem_of_getElem? hz
  rw [Array.toList_zip] at h1
  have h2 := (List.of_mem_zip h1).1
  rw [Array.toList_zip] at h2
  have h3 : z.1.1 ∈ i.g.scores := (List.of_mem_zip h2).1
  unfold Geo.scores at h3
  obtain ⟨u, hu, e3⟩ := List.mem_map.1 h3
  obtain ⟨a, b⟩ := units_mem hu
  refine ⟨u.2.1, ?_, b⟩
  rw [hc, ← e3]
  exact a

/-! ## 2 The list of plane claims -/

/-- A fold that pushes one plane claim and one unit a step: what lay in the first list stays at its
number, and each unit pushed holds the number of its own plane claim. -/
theorem fold_planes {X : Type}
    (step : Array RemP × Array ScoreP → X → Option (Array RemP × Array ScoreP))
    (hstep : ∀ acc x acc1, step acc x = some acc1 → ∃ rem k,
      acc1 = (acc.1.push rem, acc.2.push k) ∧ k.claim = acc.1.size ∧ rem.s0 = k.s0 ∧ rem.np = 5) :
    ∀ (xs : List X) (acc acc' : Array RemP × Array ScoreP), xs.foldlM step acc = some acc' →
      (∀ (n : ℕ) (pc : RemP), acc.1[n]? = some pc → acc'.1[n]? = some pc) ∧
      ∀ k ∈ acc'.2.toList, k ∈ acc.2.toList ∨
        ∃ pc : RemP, acc'.1[k.claim]? = some pc ∧ pc.s0 = k.s0 ∧ pc.np = 5
  | [], acc, acc', h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨fun _ _ h => h, fun k hk => .inl hk⟩
  | x :: xs, acc, acc', h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨acc1, h1, h2⟩ := h
    obtain ⟨rem, k0, e, hc, hs, hn⟩ := hstep acc x acc1 h1
    obtain ⟨i1, i2⟩ := fold_planes step hstep xs acc1 acc' h2
    subst e
    refine ⟨fun n pc hpc => i1 n pc ?_, fun k hk => ?_⟩
    · have hlt : n < acc.1.size := by
        by_contra hc'
        rw [Array.getElem?_eq_none (by omega)] at hpc
        exact nomatch hpc
      show (acc.1.push rem)[n]? = some pc
      rw [Array.getElem?_push, if_neg (by omega)]
      exact hpc
    · rcases i2 k hk with h3 | h3
      · have h3' : k ∈ (acc.2.push k0).toList := h3
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at h3'
        rcases h3' with h3' | rfl
        · exact .inl h3'
        · refine .inr ⟨rem, i1 _ _ ?_, hs, hn⟩
          show (acc.1.push rem)[k.claim]? = some rem
          rw [hc, Array.getElem?_push, if_pos rfl]
      · exact .inr h3

/-- **What the function of the points lays into its list of plane claims.** -/
theorem planes_spec {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : pointsOf g zk h L = some p) :
    (g.units .kr [.rm, .rd]).length = h.remainders.size ∧
    (∀ (n : ℕ) (u : ℕ × CallG × Keys) (s0 : ℕ), (g.units .kr [.rm, .rd])[n]? = some u →
      h.remainders[n]? = some s0 →
      ∃ pc : RemP, p.planes[n]? = some pc ∧ pc.call = u.1 ∧ pc.s0 = s0 ∧ pc.np = 3) ∧
    ∀ k ∈ p.scores.toList, ∃ pc : RemP, p.planes[k.claim]? = some pc ∧ pc.s0 = k.s0 ∧
      pc.np = 5 := by
  unfold pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, hkr, _, hn, a, hf, uW, _, uX, _, uH, _, _, hs, _, _, e⟩ := hp
  rw [← Array.foldlM_toList] at hf
  have hq := fold_planes _ (fun acc x acc1 h1 => by
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at h1
      obtain ⟨_, _, e1⟩ := h1
      exact ⟨_, _, e1.symm, rfl, rfl, rfl⟩) _ _ _ hf
  subst e
  refine ⟨by simpa using hkr, fun n u s0 hu hs0 => ?_, fun k hk => ?_⟩
  · refine ⟨⟨u.1, inner (g.unitAt u.1 u.2.1 u.2.2) (zk.getD u.1 #[]), u.2.2 == .rd,
      piecesOf (g.unitAt u.1 u.2.1 u.2.2) (zk.getD u.1 #[]), s0, 3⟩, hq.1 n _ ?_, rfl, rfl, rfl⟩
    have hzp : ((g.units .kr [.rm, .rd]).toArray.zip h.remainders)[n]? = some (u, s0) :=
      Array.getElem?_zip_eq_some.2 ⟨by simpa using hu, hs0⟩
    rw [Array.getElem?_map, hzp]
    rfl
  · rcases hq.2 k hk with h3 | h3
    · exact nomatch h3
    · exact h3

/-! ## 3 The plan's stretches -/

theorem planes_region : ∀ (n k j : ℕ), k ≤ j → j < k + 3 * n →
    ∃ m s0 : ℕ, (planesPlan n k)[m]? = some s0 ∧ s0 ≤ j ∧ j < s0 + 3
  | 0, k, j, h1, h2 => by omega
  | n + 1, k, j, h1, h2 => by
    by_cases c : j < k + 3
    · exact ⟨0, k, rfl, h1, c⟩
    · obtain ⟨m, s0, a, b, d⟩ := planes_region n (k + 3) j (by omega) (by omega)
      exact ⟨m + 1, s0, a, b, d⟩

theorem units_region : ∀ (us : List (ℕ × ℕ)) (k j : ℕ), k ≤ j → j < unitsNext us k →
    ∃ (m : ℕ) (u : ℕ × ℕ) (t : ℕ × ℕ × ℕ), us[m]? = some u ∧ (unitsPlan us k)[m]? = some t ∧
      t.1 ≤ j ∧ j < t.2.2 + 2 * u.2 ∧ t.2.1 = t.1 + 7 ∧ t.2.2 = t.1 + 7 + own3 u.1
  | [], k, j, h1, h2 => by
    have : j < k := h2
    omega
  | u :: us, k, j, h1, h2 => by
    by_cases c : j < k + 7 + own3 u.1 + 2 * u.2
    · exact ⟨0, u, (k, k + 7, k + 7 + own3 u.1), rfl, rfl, h1, c, rfl, rfl⟩
    · obtain ⟨m, v, t, a, b, d⟩ := units_region us (k + 7 + own3 u.1 + 2 * u.2) j (by omega) h2
      exact ⟨m + 1, v, t, a, b, d⟩

/-! ## 4 A unit's list lies in the run's -/

section Mem
variable {S : OnBytes.Attention.Shape} {gL : OnBytes.Model.Forest.Heard} {i : In} {K : ℕ}

/-- A call of the place, as the shape's. -/
theorem call_back (hg : i.g = geoOf S) {c : CallG} {q : ℕ} {t : OnBytes.Attention.Table}
    (hc : (c, q) ∈ i.g.calls.toList.zipIdx) (ht : (c.tab == tabOf t) = true) :
    ∃ y ∈ S.calls.toList.zipIdx, y.2 = q ∧ (y.1.kind == t) = true := by
  rw [hg, calls_zip] at hc
  obtain ⟨y, hy, e⟩ := List.mem_map.1 hc
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  refine ⟨y, hy, e2, ?_⟩
  rw [← tab_eq y.1.kind t]
  rw [← e1] at ht
  exact ht

/-- **A remainder unit's plane claim**: its list lies in claim 3's. -/
theorem rem_mem (hg : i.g = geoOf S) {pc : RemP} (hpc : pc ∈ i.p.planes.toList) {c : CallG}
    (hc : (c, pc.call) ∈ i.g.calls.toList.zipIdx) (ht : (c.tab == Tab.kr) = true) :
    ∀ f ∈ Fo.linPlanesT (oldOf S gL i) K (remBack pc), f ∈ Fo.claim3T (oldOf S gL i) K := by
  intro f hf
  obtain ⟨y, hy, e2, hk⟩ := call_back (t := .kr) hg hc ht
  refine List.mem_flatMap.2 ⟨y, hy, ?_⟩
  rw [if_pos hk]
  refine List.mem_append_left _ (List.mem_flatMap.2 ⟨remBack pc, ?_, ?_⟩)
  · show remBack pc ∈ (i.p.planes.map remBack).toList
    rw [Array.toList_map]
    exact List.mem_map.2 ⟨pc, hpc, rfl⟩
  · rw [if_pos (show ((remBack pc).call == y.2) = true by
      rw [e2]
      exact beq_self_eq_true _)]
    exact List.mem_append_left _ hf

/-- **A softmax-table unit**: its list lies in claim 4's. -/
theorem unit_mem (hg : i.g = geoOf S) (hv : Visited i) {z : ScoreP × ℕ}
    (hz : z ∈ i.p.scores.toList.zipIdx) :
    ∀ f ∈ Fo.unitKFDT (oldOf S gL i) K z.2 (scoreBack z.1), f ∈ Fo.claim4T (oldOf S gL i) K := by
  intro f hf
  obtain ⟨c, hc, ht⟩ := hv z.1
    (List.mem_zipIdx_iff_getElem?.1 hz |> fun e => List.mem_of_getElem? e)
  obtain ⟨y, hy, e2, hk⟩ := call_back (t := .kfd) hg hc ht
  refine List.mem_flatMap.2 ⟨y, hy, ?_⟩
  rw [if_pos hk]
  refine List.mem_append_left _ (List.mem_flatMap.2 ⟨(scoreBack z.1, z.2), ?_, ?_⟩)
  · rw [old_scores_zip]
    exact List.mem_map.2 ⟨z, hz, rfl⟩
  · rw [if_pos (show ((scoreBack z.1).call == y.2) = true by
      rw [e2]
      exact beq_self_eq_true _)]
    exact List.mem_append_left _ hf

end Mem


/-- A member of an array all of whose members pass a test. -/
theorem all_of_get {α : Type} {a : Array α} {p : α → Bool} (h : a.all p = true) {m : ℕ} {v : α}
    (hv : a.toList[m]? = some v) : p v = true := by
  obtain ⟨hm, e⟩ := List.getElem?_eq_some_iff.1 hv
  have h1 : p a[m] = true := Array.all_eq_true.1 h m (by simpa using hm)
  rw [← e]
  simpa using h1

/-! ## 5 The run "first" -/

section Main
variable {x : OnBytes.Params.AttentionRounds} {F G F' : Fork} {rs rest : List Fmt.RoundView} {lead : ℕ}
  {h : Heard} {i : In} {zk : Array (Array E)} {l : Left} {K : ℕ} {l₁ : List Aff} {jn : JoinsP}

/-- **Every slot of the rounds' own, from the first up to the two value products' scalars, but the
accumulator's, is named with a coefficient that does not read 0 by a form of the run "first"**,
CONDITIONAL on the premises that the head lists. -/
theorem k5_live_first (A : OnBytes.Attention.Plan) (S : OnBytes.Attention.Shape)
    (gL : OnBytes.Model.Forest.Heard)
    (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : OnBytes.Model.Road.Sized F)
    (li : LeftIs i.g zk h F' l) (hp : pointsOf i.g zk h l = some i.p) (gf : LiveFits i.g x)
    (hg : i.g = geoOf S) (hzk : i.zk = gL.zk) (hN : A.NC = S.calls.size)
    (h1 : firstRun i K = some (l₁, jn)) (hL : heardLive h = true) :
    ∀ j, F.next ≤ j → j < kV x F.next → j ≠ kB x F.next →
      ∃ f ∈ l₁, slotCo Reading.gl f j ≠ 0 := by
  have PA := points_are hp
  obtain ⟨fU, ⟨SE, eE⟩, _⟩ := li.forms
  have Q := heard5_of hh hz
  have hv := visited_of PA
  obtain ⟨pl0, pl1, pl2⟩ := planes_spec hp
  rw [(first_any A S gL i K l₁ jn hg hzk hN h1).1]
  unfold heardLive at hL
  simp only [Bool.and_eq_true] at hL
  obtain ⟨⟨⟨⟨⟨⟨⟨lU, lE⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hL
  obtain ⟨H, hH⟩ : ∃ H, H = oldOf S gL i := ⟨_, rfl⟩
  rw [← hH]
  obtain ⟨k, hk⟩ : ∃ k, k = F.next := ⟨_, rfl⟩
  rw [← hk] at Q ⊢
  have in3 : ∀ f ∈ Fo.claim3T H K, f ∈ Fo.claim3T H K ++ (Fo.claim4T H K ++ Fo.claim5T H K) :=
    fun f hf => List.mem_append_left _ hf
  have in4 : ∀ f ∈ Fo.claim4T H K, f ∈ Fo.claim3T H K ++ (Fo.claim4T H K ++ Fo.claim5T H K) :=
    fun f hf => List.mem_append_right _ (List.mem_append_left _ hf)
  have in5 : ∀ f ∈ Fo.claim5T H K, f ∈ Fo.claim3T H K ++ (Fo.claim4T H K ++ Fo.claim5T H K) :=
    fun f hf => List.mem_append_right _ (List.mem_append_right _ hf)
  have b0 : kB x k = unitsNext x.score (k + 3 * x.planeMessages) := rfl
  intro j j1 j2 j3
  by_cases c1 : j < k + 3 * x.planeMessages
  · -- a remainder unit's three scalars
    obtain ⟨m, s0, a, b, d⟩ := planes_region x.planeMessages k j j1 c1
    have nP : h.remainders.toList = planesPlan x.planeMessages k := congrArg Nums.planes Q.nums
    have hr : h.remainders[m]? = some s0 := by
      rw [← Array.getElem?_toList, nP]
      exact a
    have hm : m < (i.g.units .kr [.rm, .rd]).length := by
      rw [pl0]
      by_contra hc
      rw [Array.getElem?_eq_none (by omega)] at hr
      exact nomatch hr
    obtain ⟨pc, hpc', e1, e2, e3⟩ := pl1 m _ s0 (List.getElem?_eq_getElem hm) hr
    obtain ⟨ua, ub⟩ := units_mem (List.getElem_mem hm)
    have hmem : pc ∈ i.p.planes.toList := by
      rw [← Array.getElem?_toList] at hpc'
      exact List.mem_of_getElem? hpc'
    obtain ⟨f, hf, hl⟩ := planes_live Reading.gl H K (remBack pc) (x := j - s0) (by
      show j - s0 < pc.np
      omega)
    refine ⟨f, in3 f ?_, ?_⟩
    · rw [hH] at hf ⊢
      exact rem_mem hg hmem (by rw [e1]; exact ua) ub f hf
    · have e : (remBack pc).s0 + (j - s0) = j := by
        show pc.s0 + (j - s0) = j
        omega
      rw [e] at hl
      exact hl
  by_cases c2 : j < kB x k
  · -- a softmax-table unit's seven scalars, its sumcheck's own slots, its end values
    obtain ⟨m, u, t, a, b, t1, t2, t3, t4⟩ :=
      units_region x.score (k + 3 * x.planeMessages) j (by omega) c2
    have nU : h.scores.toList.map (fun o => (o.1, o.2.first, o.2.sEnd)) =
        unitsPlan x.score (k + 3 * x.planeMessages) := congrArg Nums.units Q.nums
    have g1 : (h.scores.toList.map fun o => (o.1, o.2.first, o.2.sEnd))[m]? = some t := by
      rw [nU]
      exact b
    rw [List.getElem?_map] at g1
    obtain ⟨o, ho, eo⟩ := Option.map_eq_some_iff.1 g1
    obtain ⟨o', ho', R⟩ := forall2_left Q.units m u a
    obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
    have g2 : (((i.g.scores.toArray.zip h.scores).zip l.scores).toList.map (·.1.2))[m]? =
        some o := by
      rw [K5Law.zipped_mid PA]
      exact ho
    rw [List.getElem?_map] at g2
    obtain ⟨z, hz', ez⟩ := Option.map_eq_some_iff.1 g2
    obtain ⟨kk, hkk, ⟨ksc, _, ks0, kpw⟩, _⟩ := forall2_right PA.units m z hz'
    rw [Array.toList_zip] at hz'
    obtain ⟨hz1, hz2⟩ := List.getElem?_zip_eq_some.1 hz'
    obtain ⟨f', hf', S0, eS⟩ := forall2_left fU m z.1 hz1
    obtain rfl : z.2 = f' := Option.some.inj (hz2.symm.trans hf')
    rw [Array.toList_zip] at hz1
    have hug : i.g.scores[m]? = some z.1.1 := (List.getElem?_zip_eq_some.1 hz1).1
    obtain ⟨ug, hug', qu⟩ := forall2_left gf.pieces m u a
    obtain rfl : z.1.1 = ug := Option.some.inj (hug.symm.trans hug')
    have hkm : kk ∈ i.p.scores.toList := List.mem_of_getElem? hkk
    have hzi : (kk, m) ∈ i.p.scores.toList.zipIdx := List.mem_zipIdx_iff_getElem?.2 hkk
    obtain ⟨c, hc, ht⟩ := hv kk hkm
    obtain ⟨tb, pc, htb, hpc'⟩ := visited_some i K _ h1 c kk.call hc ht kk m hzi
      (beq_self_eq_true _)
    obtain ⟨pc', hq, p1, p2⟩ := pl2 kk hkm
    obtain rfl : pc = pc' := Option.some.inj (hpc'.symm.trans hq)
    have y1 : H.t.score[m]? = some (tbBack tb) := by
      rw [hH, old_score, htb]
      rfl
    have y2 : H.planes[(scoreBack kk).claim]? = some (remBack pc) := by
      rw [hH]
      show (oldOf S gL i).planes[kk.claim]? = _
      rw [old_plane, hpc']
      rfl
    have into : ∀ f ∈ Fo.unitKFDT H K m (scoreBack kk),
        f ∈ Fo.claim3T H K ++ (Fo.claim4T H K ++ Fo.claim5T H K) := fun f hf => in4 f (by
      rw [hH] at hf ⊢
      exact unit_mem hg hv hzi f hf)
    have q1 : o.1 = t.1 := congrArg (·.1) eo
    have q2 : o.2.first = t.2.1 := congrArg (·.2.1) eo
    have q3 : o.2.sEnd = t.2.2 := congrArg (·.2.2) eo
    have q0 : kk.s0 = o.1 := by rw [ks0, ← ez]
    have qe : kk.sc.ends = o.2.sEnd := by
      rw [ksc, ← ez]
      rfl
    have qr : (scoreBack kk).sc.rowU = formOf o.2 S0 {} := by
      show kk.sc.row = _
      rw [ksc, ← ez]
      exact eS
    have qp : (scoreBack kk).pw.size = z.1.1.pcs.length := by
      show (kk.pw.map _).size = _
      rw [Array.size_map, kpw, piecesOf_size]
    have lo : sumLive true o.2 = true := all_of_get lU ho
    have via : ((∃ y < (remBack pc).np, j = (remBack pc).s0 + y) ∨ j = (scoreBack kk).s0 + 5 ∨
        ∃ e < 2 * (scoreBack kk).pw.size, j = (scoreBack kk).sc.sEnd + e) →
        ∃ f ∈ Fo.claim3T H K ++ (Fo.claim4T H K ++ Fo.claim5T H K),
          slotCo Reading.gl f j ≠ 0 := fun hj => by
      obtain ⟨f, hf, hl⟩ := unit_live Reading.gl H K y1 y2 hj
      exact ⟨f, into f hf, hl⟩
    by_cases d1 : j < t.1 + 5
    · refine via (.inl ⟨j - t.1, ?_, ?_⟩)
      · show j - t.1 < pc.np
        omega
      · show j = pc.s0 + (j - t.1)
        omega
    by_cases d2 : j = t.1 + 5
    · refine via (.inr (.inl ?_))
      show j = kk.s0 + 5
      omega
    by_cases d3 : j = t.1 + 6
    · -- the seventh scalar: inside the row's claimed sum alone
      refine ⟨_, into _ (unit_row H K y1 y2), ?_⟩
      rw [qr]
      exact rec_start_live R lo S0 (by omega) (by
        rw [slotCo_slot, if_pos (by omega)]
        exact one_ne_zero)
    by_cases d4 : j < t.2.2
    · refine ⟨_, into _ (unit_row H K y1 y2), ?_⟩
      rw [qr]
      exact rec_own_live R (plain4_d _) lo S0 (by omega) (by
        show j < o.2.first + own3 u.1
        omega) (by rw [slotCo_slot, if_neg (by omega)])
    · refine via (.inr (.inr ⟨j - t.2.2, by omega, ?_⟩))
      show j = kk.sc.ends + (j - t.2.2)
      omega
  -- the five, the index's bits, the two; "denominator times output"
  have hNP : H.S.NP = x.pairs := by
    have e := gf.NP
    rw [hg] at e
    rw [hH]
    exact e
  have hlt : H.S.cf.lt = x.lt := by
    have e := gf.lt
    rw [hg] at e
    rw [hH]
    exact e
  have m5 : h.five = kB x k := congrArg Nums.five Q.nums
  have n5 : H.d.s5 = kB x k := by
    rw [hH]
    exact PA.s5.trans m5
  have nIB : H.d.sIB = kB x k + 5 := by
    rw [hH]
    exact PA.sIB.trans (congrArg Nums.bits Q.nums)
  have n5h : H.d.s5h = kB x k + 5 + x.lt := by
    rw [hH]
    exact PA.s5h.trans (congrArg Nums.two Q.nums)
  have fE : h.division.first = kE x k := congrArg Nums.fE Q.nums
  have sE : H.d.scE.sEnd = kE x k + own3 x.e := by
    rw [hH]
    show i.p.d.scE.ends = _
    rw [PA.scE]
    exact congrArg Nums.eE Q.nums
  have wE : H.d.scE.rowU = formOf h.division SE {} := by
    rw [hH]
    show i.p.d.scE.row = _
    rw [PA.scE]
    exact eE
  have a1 : kE x k = kB x k + 5 + x.lt + 2 := rfl
  have a2 : kV x k = kE x k + own3 x.e + 2 * x.pairs := rfl
  have via5 : (j = H.d.s5 + 2 ∨ j = H.d.s5 + 3 ∨ j = H.d.s5 + 4 ∨
      (∃ k < H.S.cf.lt, j = H.d.sIB + k) ∨ j = H.d.s5h ∨ j = H.d.s5h + 1 ∨
      ∃ e < 2 * H.S.NP, j = H.d.scE.sEnd + e) →
      ∃ f ∈ Fo.claim3T H K ++ (Fo.claim4T H K ++ Fo.claim5T H K),
        slotCo Reading.gl f j ≠ 0 := fun hj => by
    obtain ⟨f, hf, hl⟩ := live5 Reading.gl H K hj
    exact ⟨f, in5 f hf, hl⟩
  by_cases d1 : j = kB x k + 1
  · -- the second of the five: inside the row's claimed sum alone
    refine ⟨_, in5 _ (row5 H K), ?_⟩
    rw [wE]
    exact rec_start_live Q.rE lE SE (by omega) (by
      rw [slotCo_slot, if_pos (by omega)]
      exact one_ne_zero)
  by_cases d2 : j = kB x k + 2
  · exact via5 (.inl (by omega))
  by_cases d3 : j = kB x k + 3
  · exact via5 (.inr (.inl (by omega)))
  by_cases d4 : j = kB x k + 4
  · exact via5 (.inr (.inr (.inl (by omega))))
  by_cases d5 : j < kB x k + 5 + x.lt
  · exact via5 (.inr (.inr (.inr (.inl ⟨j - H.d.sIB, by omega, by omega⟩))))
  by_cases d6 : j = kB x k + 5 + x.lt
  · exact via5 (.inr (.inr (.inr (.inr (.inl (by omega))))))
  by_cases d7 : j = kB x k + 5 + x.lt + 1
  · exact via5 (.inr (.inr (.inr (.inr (.inr (.inl (by omega)))))))
  by_cases d8 : j < kE x k + own3 x.e
  · refine ⟨_, in5 _ (row5 H K), ?_⟩
    rw [wE]
    exact rec_own_live Q.rE (plain4_d _) lE SE (by omega) (by rw [fE]; exact d8)
      (by rw [slotCo_slot, if_neg (by omega)])
  · exact via5 (.inr (.inr (.inr (.inr (.inr (.inr ⟨j - H.d.scE.sEnd, by omega, by omega⟩))))))

end Main

end H2K5.Honest

#print axioms H2K5.Honest.units_mem
#print axioms H2K5.Honest.forall2_left
#print axioms H2K5.Honest.forall2_right
#print axioms H2K5.Honest.visited_of
#print axioms H2K5.Honest.fold_planes
#print axioms H2K5.Honest.planes_spec
#print axioms H2K5.Honest.planes_region
#print axioms H2K5.Honest.units_region
#print axioms H2K5.Honest.call_back
#print axioms H2K5.Honest.rem_mem
#print axioms H2K5.Honest.unit_mem
#print axioms H2K5.Honest.all_of_get
#print axioms H2K5.Honest.k5_live_first
