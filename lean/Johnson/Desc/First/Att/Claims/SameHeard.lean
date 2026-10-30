-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/SameHeard.lean: kind K5: the record made of what was heard agrees with
the blank one in what is public (Same, Johnson/Desc/First/Att/Claims/Same.lean), where what was
heard has the place's lengths. So the dry run's yes gives the runs' return, and the numbers of their
claims, at every such record.

Main names:
  `forall₂_of_get`; `sameW_pieces`: a unit's pieces, by layer and head, are the same at every key
    point; `innerSize_one`; `div_pub`: what pointsOf lays of the division that is public.
  `LensOne zk zk' h h'`: two hearings have one set of lengths. `same_pts`: SameP at what pointsOf
    returns at both. `pointM_size`, `pointD_size`. `same_of_lens`: Same at two records made at one
    geometry (starts_one, Johnson/Desc/First/Att/Claims/SameTabs.lean).
  `same_of_heard`: Same i (blankIn c p0 t0). `chal_blank`. `HeardLens g zk h`: the lengths as
    numbers of the place; `lensOne_of`.
  `lens_heard`: where claimsOk says yes there are two numbers n₁ and n₂, chosen before the record,
    that the lengths of the lists of "first" and of "second" are at every record made by pointsOf
    and tablesP of a hearing with HeardLens.
Premises, not shown in this file or in what it imports: HeardLens (the hearing's half's and the
lookup's kind's); the return of pointsOf and tablesP.
Limit: the two numbers are numbers of c, K, k3, planesOk and nzx: one K for the dry run and the
record.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.SameTabs
import Johnson.Desc.First.Att.Claims.Returns
import Johnson.Desc.First.Att.Claims.PlanesAre
import Johnson.Desc.First.Att.Claims.Place
import Johnson.Desc.First.Att.Claims.LenSame

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo UnitG W1 RemP ScoreP DivP Pts Heard Left TablesP LookIn ParC)
open VerifiableInference.Desc.First.Att.P.Runs (In)
open VerifiableInference.Desc.Part (MaskedSum.Heard)

/-- Two lists of one length whose members of one number are related. -/
theorem forall₂_of_get {α α' : Type} {R : α → α' → Prop} :
    ∀ (l : List α) (l' : List α'), l.length = l'.length →
      (∀ (n : ℕ) a b, l[n]? = some a → l'[n]? = some b → R a b) → List.Forall₂ R l l'
  | [], [], _, _ => .nil
  | a :: l, b :: l', hl, h => .cons (h 0 a b rfl rfl)
      (forall₂_of_get l l' (by simpa using hl) fun n x y hx hy => h (n + 1) x y (by simpa using hx) (by simpa using hy))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- A unit's pieces, by layer and head, are the same at every key point. -/
theorem sameW_pieces (u : UnitG) (k k' : Array E) : SameW (P.piecesOf u k) (P.piecesOf u k') := by
  have key : ∀ z : Array E, (P.piecesOf u z).toList.map (fun w => (w.lam, w.a)) =
      (u.pcs.map fun pc => (pc.lam, pc.a)).mergeSort
        fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 ≤ y.2) := by
    intro z
    unfold P.piecesOf
    rw [List.toList_toArray, List.map_mergeSort (f := fun w : W1 => (w.lam, w.a))
      (s := fun x y => decide (x.1 < y.1) || (x.1 == y.1 && decide (x.2 ≤ y.2))) (fun _ _ _ _ => rfl), List.map_map]
    rfl
  have e := (key k).trans (key k').symm
  unfold SameW
  refine forall₂_of_get _ _ (by have := congrArg List.length e; simpa using this) fun n a b ha hb => ?_
  have e' := congrArg (fun l => l[n]?) e
  simp only [List.getElem?_map, ha, hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e'
  exact e'

theorem innerSize_one (u : UnitG) {k k' : Array E} (h : k.size = k'.size) :
    (P.inner u k).size = (P.inner u k').size := by
  unfold P.inner
  rw [Array.size_extract, Array.size_extract, h]

/-- What pointsOf lays of the division that is public. -/
theorem div_pub {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : P.pointsOf g zk h L = some p) :
    ∃ uW uX uH, g.single .wl = some uW ∧ g.single .ix = some uX ∧ g.single .wh = some uH ∧
      p.d.pwW = P.piecesOf uW (zk.getD uW.call #[]) ∧ p.d.pwX = P.piecesOf uX (zk.getD uX.call #[]) ∧
      p.d.pwH = P.piecesOf uH (zk.getD uH.call #[]) ∧ p.d.qWH = uH.call ∧ p.d.zcW.size = g.ldh ∧
      p.d.zcH.size = g.ldh ∧ p.d.ziW.size = g.lt := by
  unfold P.pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, hr, _, hn, a, hf, uW, hW, uX, hX, uH, hH, _, hs, _, hz, e⟩ := hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hz
  subst e
  refine ⟨uW, uX, uH, hW, hX, hH, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · show ((P.inner uW (zk.getD uW.call #[])).extract (1 + g.lgk + g.lt) (1 + g.lgk + g.lt + g.ldh)).size = _
    rw [Array.size_extract, hz.1.1]
    omega
  · show ((P.inner uH (zk.getD uH.call #[])).extract (g.lgk + g.lt) (g.lgk + g.lt + g.ldh)).size = _
    rw [Array.size_extract, hz.2]
    omega
  · show ((P.inner uW (zk.getD uW.call #[])).extract (1 + g.lgk) (1 + g.lgk + g.lt)).size = _
    rw [Array.size_extract, hz.1.1]
    omega

/-- Two hearings at one geometry have one set of lengths: the calls' key points; the challenges of the units' sumchecks, of the score's at the index, and of the two value products'. -/
structure LensOne (zk zk' : Array (Array E)) (h h' : Heard) : Prop where
  zk : ∀ q, (zk.getD q #[]).size = (zk'.getD q #[]).size
  scores : ∀ (n : ℕ) o o', h.scores[n]? = some o → h'.scores[n]? = some o' →
    (P.chal o.2).size = (P.chal o'.2).size
  atIndex : (P.chal h.atIndex).size = (P.chal h'.atIndex).size
  below : (P.chal h.below).size = (P.chal h'.below).size
  on : (P.chal h.on).size = (P.chal h'.on).size

variable {g : Geo} {zk zk' : Array (Array E)} {h h' : Heard} {L L' : Left} {p p' : Pts}

/-- **What the claims read agrees in what is public**, at two hearings of one set of lengths. -/
theorem same_pts (hp : P.pointsOf g zk h L = some p) (hp' : P.pointsOf g zk' h' L' = some p')
    (Z : LensOne zk zk' h h') : SameP p p' := by
  have A := planes_are hp
  have A' := planes_are hp'
  have B := points_are hp
  have B' := points_are hp'
  obtain ⟨_, c1, c2⟩ := points_counts hp
  obtain ⟨_, c1', c2'⟩ := points_counts hp'
  have nR : h.remainders.size = h'.remainders.size := A.nR.symm.trans A'.nR
  have nS : h.scores.size = h'.scores.size := B.nH.symm.trans B'.nH
  have remS : ∀ (u : ℕ × P.CallG × P.Keys) (s0 s0' : ℕ), SameRem (remAt g zk u s0) (remAt g zk' u s0') :=
    fun u _ _ => ⟨rfl, innerSize_one _ (Z.zk _), rfl, sameW_pieces _ _ _, rfl⟩
  have unitS : ∀ (u : UnitG) (s0 s0' : ℕ), SameRem (remOfUnit zk u s0) (remOfUnit zk' u s0') :=
    fun u _ _ => ⟨rfl, innerSize_one _ (Z.zk _), rfl, sameW_pieces _ _ _, rfl⟩
  have some_of_lt : ∀ {β : Type} (a : Array β) (n : ℕ), n < a.size → ∃ x, a[n]? = some x :=
    fun a n hn => ⟨_, Array.getElem?_eq_getElem hn⟩
  have someL : ∀ {β : Type} (l : List β) (n : ℕ), n < l.length → ∃ x, l[n]? = some x :=
    fun l n hn => ⟨_, List.getElem?_eq_getElem hn⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine forall₂_of_get _ _ (by rw [Array.length_toList, Array.length_toList, c1, c1', nR, nS])
      fun n a b ha hb => ?_
    rw [Array.getElem?_toList] at ha hb
    rcases Nat.lt_or_ge n h.remainders.size with hn | hn
    · obtain ⟨u, hu⟩ := someL (g.units .kr [.rm, .rd]) n (by rw [A.nR]; exact hn)
      obtain ⟨s0, h0⟩ := some_of_lt h.remainders n hn
      obtain ⟨s0', h0'⟩ := some_of_lt h'.remainders n (nR ▸ hn)
      rw [A.rem n u s0 hu h0] at ha
      rw [A'.rem n u s0' hu h0'] at hb
      rw [← Option.some.inj ha, ← Option.some.inj hb]
      exact remS u s0 s0'
    · have hlt : n < p.planes.size := by
        rcases Nat.lt_or_ge n p.planes.size with h1 | h1
        · exact h1
        · rw [Array.getElem?_eq_none h1] at ha; cases ha
      have hm : n - h.remainders.size < h.scores.size := by omega
      obtain ⟨u, hu⟩ := someL g.scores (n - h.remainders.size) (by rw [B.nH]; exact hm)
      obtain ⟨o, ho⟩ := some_of_lt h.scores _ hm
      obtain ⟨o', ho'⟩ := some_of_lt h'.scores (n - h.remainders.size) (nS ▸ hm)
      obtain ⟨k, _, kc, kp, _⟩ := A.unit _ u o hu ho
      obtain ⟨k', _, kc', kp', _⟩ := A'.unit _ u o' hu ho'
      have e1 : k.claim = n := by rw [kc]; omega
      have e2 : k'.claim = n := by rw [kc', ← nR]; omega
      rw [e1, ha] at kp
      rw [e2, hb] at kp'
      rw [Option.some.inj kp, Option.some.inj kp']
      exact unitS u _ _
  · refine forall₂_of_get _ _ (by rw [Array.length_toList, Array.length_toList, c2, c2', nS])
      fun n a b ha hb => ?_
    rw [Array.getElem?_toList] at ha hb
    have hn : n < h.scores.size := by
      rcases Nat.lt_or_ge n p.scores.size with h1 | h1
      · rw [← c2]; exact h1
      · rw [Array.getElem?_eq_none h1] at ha; cases ha
    obtain ⟨u, hu⟩ := someL g.scores n (by rw [B.nH]; exact hn)
    obtain ⟨o, ho⟩ := some_of_lt h.scores n hn
    obtain ⟨o', ho'⟩ := some_of_lt h'.scores n (nS ▸ hn)
    obtain ⟨k, hk, kc, _, _, _, kw, _⟩ := A.unit n u o hu ho
    obtain ⟨k', hk', kc', _, _, _, kw', _⟩ := A'.unit n u o' hu ho'
    rw [ha] at hk
    rw [hb] at hk'
    obtain rfl := Option.some.inj hk
    obtain rfl := Option.some.inj hk'
    have call : ∀ {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts} (H : PointsAre g zk h L p) {k : ScoreP},
        p.scores[n]? = some k → k.call = u.call := by
      intro zk h L p H k hk
      have e := congrArg (fun l => l[n]?) (calls_are H)
      simp only [List.getElem?_map, Array.getElem?_toList, hk, hu, Option.map_some, Option.some.injEq] at e
      exact e
    have chal : ∀ {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts} (H : PointsAre g zk h L p) {k : ScoreP}
        {o : ℕ × MaskedSum.Heard}, p.scores[n]? = some k → h.scores[n]? = some o → k.sc.r = P.chal o.2 := by
      intro zk h L p H k o hk ho
      have e := congrArg (fun l => l[n]?) (chal_are H)
      simp only [List.getElem?_map, Array.getElem?_toList, hk, ho, Option.map_some, Option.some.injEq] at e
      exact e
    exact ⟨(call B ha).trans (call B' hb).symm, by rw [kc, kc', nR], by rw [kw, kw']; exact sameW_pieces _ _ _,
      by rw [chal B ha ho, chal B' hb ho']; exact Z.scores n o o' ho ho'⟩
  · obtain ⟨uW, uX, uH, a1, a2, a3, w1, w2, w3, q, z1, z2, _⟩ := div_pub hp
    obtain ⟨uW', uX', uH', b1, b2, b3, w1', w2', w3', q', z1', z2', _⟩ := div_pub hp'
    obtain rfl := Option.some.inj (a1.symm.trans b1)
    obtain rfl := Option.some.inj (a2.symm.trans b2)
    obtain rfl := Option.some.inj (a3.symm.trans b3)
    exact ⟨by rw [w1, w1']; exact sameW_pieces _ _ _, by rw [w2, w2']; exact sameW_pieces _ _ _,
      by rw [w3, w3']; exact sameW_pieces _ _ _, q.trans q'.symm, z1.trans z1'.symm, z2.trans z2'.symm⟩
  · rw [B.scF, B'.scF]
    exact Z.atIndex

theorem pointM_size {d d' : DivP} (h1 : d.vpm.r.size = d'.vpm.r.size) (h2 : d.ziW.size = d'.ziW.size) :
    (P.pointM g d).size = (P.pointM g d').size := by
  unfold P.pointM DivP.zilo P.lastCoords
  simp only [Array.size_append, Array.size_extract, h1, h2]

theorem pointD_size {d d' : DivP} (h1 : d.vpd.r.size = d'.vpd.r.size) (h2 : d.ziW.size = d'.ziW.size) :
    (P.pointD g d).size = (P.pointD g d').size := by
  unfold P.pointD DivP.zilo P.lastCoords
  simp only [Array.size_append, Array.size_extract, h1, h2]

/-- **Two records made at one geometry, of two hearings of one set of lengths, agree in what is public.** -/
theorem same_of_lens {mats : Array (ℕ × ℕ)} {nW nW' : ℕ} {lk lk' : LookIn} {i i' : In}
    (hg : i.g = g) (hg' : i'.g = g) (hp : P.pointsOf g zk h L = some i.p) (hp' : P.pointsOf g zk' h' L' = some i'.p)
    (ht : P.tablesP g mats nW lk i.p = some i.t) (ht' : P.tablesP g mats nW' lk' i'.p = some i'.t)
    (Z : LensOne zk zk' h h') : Same i i' := by
  have Sp := same_pts hp hp' Z
  have B := points_are hp
  have B' := points_are hp'
  obtain ⟨_, _, c2⟩ := points_counts hp
  obtain ⟨_, _, c2'⟩ := points_counts hp'
  have hs : i.p.scores.size = i'.p.scores.size := by rw [c2, c2', ← B.nH, ← B'.nH]
  obtain ⟨St, ⟨m1, d1⟩, m2, d2⟩ := starts_one hs ht ht'
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, zi⟩ := div_pub hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, zi'⟩ := div_pub hp'
  have hzi : i.p.d.ziW.size = i'.p.d.ziW.size := zi.trans zi'.symm
  refine ⟨hg.trans hg'.symm, Sp, ⟨?_, ?_, St.tA, St.tVM, St.tVD, St.score, St.hW, St.hX, St.hE, St.hT, St.hPi,
    St.hR2, St.tO, St.qO, St.qVM, St.qVD, St.qF, St.qKx, St.tabLen⟩⟩
  · rw [m1, m2]
    exact pointM_size (by rw [B.vpm, B'.vpm]; exact Z.below) hzi
  · rw [d1, d2]
    exact pointD_size (by rw [B.vpd, B'.vpd]; exact Z.on) hzi

/-- **The record made of what was heard agrees with the blank one in what is public**, where what was heard has the blank hearing's lengths. -/
theorem same_of_heard {c : ParC} {lk : LookIn} {planesOk : Bool} {nzx : ℕ} {p0 : Pts} {t0 : TablesP} {i : In}
    (hg : i.g = c.geo) (hp : P.pointsOf c.geo zk h L = some i.p)
    (ht : P.tablesP c.geo c.mats c.nW lk i.p = some i.t) (hp0 : P.blankPts c.geo = some p0)
    (ht0 : P.tablesP c.geo c.mats c.nW (Spec.blankLook c.geo planesOk nzx) p0 = some t0)
    (Z : LensOne zk (P.blankZk c.geo) h (P.blankHeard c.geo)) : Same i (Spec.blankIn c p0 t0) :=
  same_of_lens (i' := Spec.blankIn c p0 t0) hg rfl hp hp0 ht ht0 Z

/-- The blank sumcheck of n variables has n challenges. -/
theorem chal_blank (n : ℕ) : (P.chal (P.blankSum n)).size = n := by
  unfold P.chal P.blankSum
  simp

/-- What was heard has the place's lengths: each call's key point as many coordinates as the call has key bits; the sumchecks' challenges as many as their variables. -/
structure HeardLens (g : Geo) (zk : Array (Array E)) (h : Heard) : Prop where
  nzk : zk.size = g.calls.size
  zk : ∀ (q : ℕ) c, g.calls[q]? = some c → (zk.getD q #[]).size = c.n
  scores : ∀ (n : ℕ) u o, g.scores[n]? = some u → h.scores[n]? = some o → (P.chal o.2).size =
    if u.below then g.lgk + 2 * g.lnT - 1 + g.ldh else g.lgk + g.lnT + g.ldh
  atIndex : (P.chal h.atIndex).size = g.lt + g.lgk + g.ldh
  below : (P.chal h.below).size = g.lgk + 2 * g.lnT - 1 + g.lB
  on : (P.chal h.on).size = g.lgk + g.lnT + g.lB

theorem lensOne_of (H : HeardLens g zk h) : LensOne zk (P.blankZk g) h (P.blankHeard g) := by
  refine ⟨fun q => ?_, fun n o o' ho ho' => ?_, ?_, ?_, ?_⟩
  · have eb : (P.blankZk g).getD q #[] = ((g.calls[q]?).map fun cc => P.zeros cc.n).getD #[] := by
      unfold P.blankZk
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    rw [eb]
    cases hc : g.calls[q]? with
    | none =>
      have hq : g.calls.size ≤ q := Array.getElem?_eq_none_iff.1 hc
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [H.nzk]; exact hq)]
      rfl
    | some c =>
      rw [H.zk q c hc]
      show c.n = (P.zeros c.n).size
      unfold P.zeros
      rw [Array.size_replicate]
  · have ho'' : (g.scores.toArray.map fun u => ((0 : ℕ), P.blankSum
        (if u.below then g.lgk + 2 * g.lnT - 1 + g.ldh else g.lgk + g.lnT + g.ldh)))[n]? = some o' := ho'
    rw [Array.getElem?_map, List.getElem?_toArray] at ho''
    cases hu : g.scores[n]? with
    | none => rw [hu] at ho''; cases ho''
    | some u =>
      rw [hu] at ho''
      rw [← Option.some.inj ho'', H.scores n u o hu ho]
      exact (chal_blank _).symm
  · rw [H.atIndex]; exact (chal_blank _).symm
  · rw [H.below]; exact (chal_blank _).symm
  · rw [H.on]; exact (chal_blank _).symm

/-- **The numbers of claims of "first" and "second" at every record made of what was heard**: where the dry run on blank points says yes there are two numbers, of the plan's letters alone, that the two lists' lengths are. -/
theorem lens_heard (c : ParC) (K : ℕ) (k3 : P.Runs.PadIn) (planesOk : Bool) (nzx : ℕ)
    (hd : P.claimsOk c K k3 planesOk nzx = true) :
    ∃ n₁ n₂ : ℕ, ∀ (i : In) (zk : Array (Array E)) (h : Heard) (L : Left) (lk : LookIn), i.g = c.geo →
      P.pointsOf c.geo zk h L = some i.p → P.tablesP c.geo c.mats c.nW lk i.p = some i.t →
      HeardLens c.geo zk h →
      (∀ l j, P.Runs.firstRun i K = some (l, j) → l.length = n₁) ∧
        ∀ l, P.Runs.secondRun i K = some l → l.length = n₂ := by
  obtain ⟨p0, t0, n₁, n₂, hp0, ht0, H⟩ := Len.lens_of_dry c K k3 planesOk nzx hd
  exact ⟨n₁, n₂, fun i zk h L lk hg hp ht Z => H i (same_of_heard hg hp ht hp0 ht0 (lensOne_of Z))⟩

end K5Law
