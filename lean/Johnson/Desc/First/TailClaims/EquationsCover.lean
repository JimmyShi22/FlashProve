-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsCover.lean: what a yes of the list "K8.equations" says of the
places that its reads name: every place of the part of a vector that holds tables is named by a read;
every place that a read names lies in the vector; no place is named twice. Proved of the list's own
text.

Definitions, statements and proofs. After OnBytes/Tie/Pv/Tail/EndReads.lean (objectsF_reads),
EndCover.lean (objectsF_cover, objectsF_coverU3) and EndOnce.lean (objectsF_apart, objectsF_once),
which say the like of `verify-on-bytes`'s routine objectsF. No routine of that program is named here. USED OF THESE FILES, EACH ON RECORDS AND PLAIN DATA ALONE:
markAt, marksOf, markRead_spec, markRead_marks, markRead_once, getD_lt, tablesTile_le, PlacesApart,
PlacesApart.symm, mem_readsList (EndLoopsB's), posOf, readsList, segsOf, carry4; of the record the
plain functions markRead and tablesTile.
Main names:
  MarksRun tl l r r': the marks r, with the places of the reads of l marked one read after the other,
    are r'; each read's vector is there.
  marksRun_cover, marksRun_sizes, marksRun_reads, marksRun_once: the runFold_* laws, on it.
  eq_parts: a yes of "K8.equations", cut at eqKeys, eqCounts and the tail.
  eqTail_marks, eq_marks: the text's reads lead from marks that are all unset to marks that are all
    set, and both tilings are there.
  **K08Cover**, **K08CoverU3**, **K08Reads**, **K08Apart** (closed Props) with eq_cover, eq_coverU3,
    eq_reads, eq_apart; eq_once.
  eq_same: what the returned record has in common with the record that was handed in.
Limits: one direction, from a yes. Nothing on what the reads add (EquationsForms.lean). That the part
of U3 is the whole vector is a premise of K08CoverU3.

-/
import Johnson.Desc.First.TailClaims.EquationsForms
import OnBytes.Tie.Pv.Tail.EndOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.Tie.Pv.Tail.Port
open OnBytes.Tie.Pv.Tail (markAt marksOf markRead_spec markRead_marks markRead_once getD_lt
  tablesTile_le PlacesApart)

/-! ## The marks, one read after the other -/

/-- The marks r, with the places of the reads of l marked one read after the other, are r'; each
read's vector is there. -/
def MarksRun (tl : HTailF2) : List (HFun × Nat) → Array (Array Bool) → Array (Array Bool) → Prop
  | [], r, r' => r' = r
  | a :: l, r, r' => ∃ r1, (tl.ix.U.getD a.1.tree none).isSome = true ∧
      tl.markRead a.1 a.2 r = some r1 ∧ MarksRun tl l r1 r'

/-- After runFold_cover. -/
theorem marksRun_cover (tl : HTailF2) :
    ∀ (l : List (HFun × Nat)) (r r' : Array (Array Bool)), MarksRun tl l r r' →
      ∀ p i, markAt r' p i →
      markAt r p i ∨ ∃ x ∈ l, p = x.1.tree / 2 ∧ ∃ d, d < (tl.mats.getD x.1.mat {}).k ∧
        posOf tl x.1 x.2 d = tl.tabFirst.getD p 0 + i
  | [], r, r', h, p, i, hm => by
    obtain rfl : r' = r := h
    exact Or.inl hm
  | a :: l, r, r', h, p, i, hm => by
    obtain ⟨r1, -, hr, ht⟩ := h
    rcases marksRun_cover tl l r1 r' ht p i hm with h1 | ⟨x, hx, e, d, d1, d2⟩
    · rcases markRead_marks tl a.1 a.2 _ _ hr p i h1 with h2 | ⟨e, d, d1, d2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨a, List.mem_cons_self, e, d, d1, d2⟩
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, e, d, d1, d2⟩

/-- After runFold_sizes. -/
theorem marksRun_sizes (tl : HTailF2) :
    ∀ (l : List (HFun × Nat)) (r r' : Array (Array Bool)), MarksRun tl l r r' →
      ∀ p, marksOf r' p = marksOf r p
  | [], r, r', h, p => by
    obtain rfl : r' = r := h
    rfl
  | a :: l, r, r', h, p => by
    obtain ⟨r1, -, hr, ht⟩ := h
    exact (marksRun_sizes tl l r1 r' ht p).trans ((markRead_spec tl a.1 a.2 _ _ hr).1 p)

/-- After runFold_marks. -/
theorem marksRun_reads (tl : HTailF2) (len : Nat → Nat) :
    ∀ (l : List (HFun × Nat)) (r r' : Array (Array Bool)), MarksRun tl l r r' →
      (∀ p, marksOf r p = len p) →
      ∀ x ∈ l, (tl.ix.U.getD x.1.tree none).isSome = true ∧
        ∀ d, d < (tl.mats.getD x.1.mat {}).k →
          posOf tl x.1 x.2 d < tl.tabFirst.getD (x.1.tree / 2) 0 + len (x.1.tree / 2)
  | [], _, _, _, _ => fun _ hx => absurd hx (List.not_mem_nil)
  | a :: l, r, r', h, h0 => by
    obtain ⟨r1, hs, hm, hr⟩ := h
    obtain ⟨e1, e2⟩ := markRead_spec tl a.1 a.2 _ _ hm
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · refine ⟨hs, fun d hd => ?_⟩
      rw [← h0]
      exact e2 d hd
    · exact marksRun_reads tl len l r1 r' hr (fun p => (e1 p).trans (h0 p)) x hx

/-- After runFold_once. -/
theorem marksRun_once (tl : HTailF2) :
    ∀ (l : List (HFun × Nat)) (r r' : Array (Array Bool)), MarksRun tl l r r' →
      (∀ q i, markAt r q i → markAt r' q i) ∧
      (∀ x ∈ l, ∀ d, d < (tl.mats.getD x.1.mat {}).k →
        tl.tabFirst.getD (x.1.tree / 2) 0 ≤ posOf tl x.1 x.2 d ∧
        ¬ markAt r (x.1.tree / 2) (posOf tl x.1 x.2 d - tl.tabFirst.getD (x.1.tree / 2) 0) ∧
        markAt r' (x.1.tree / 2) (posOf tl x.1 x.2 d - tl.tabFirst.getD (x.1.tree / 2) 0)) ∧
      (∀ x ∈ l, ∀ d d', d < d' → d' < (tl.mats.getD x.1.mat {}).k →
        posOf tl x.1 x.2 d ≠ posOf tl x.1 x.2 d') ∧
      l.Pairwise (PlacesApart tl)
  | [], r, r', h => by
    obtain rfl : r' = r := h
    exact ⟨fun _ _ hm => hm, fun _ hx => absurd hx (List.not_mem_nil),
      fun _ hx => absurd hx (List.not_mem_nil), List.Pairwise.nil⟩
  | a :: l, r, r', h => by
    obtain ⟨r0, -, hr, ht⟩ := h
    obtain ⟨r1, r2, r3⟩ := markRead_once tl a.1 a.2 _ _ hr
    obtain ⟨i1, i2, i3, i4⟩ := marksRun_once tl l r0 r' ht
    refine ⟨fun q i hm => i1 q i (r1 q i hm), fun x hx d hd => ?_, fun x hx => ?_,
      List.pairwise_cons.2 ⟨fun y hy e d hd d' hd' he => ?_, i4⟩⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · obtain ⟨a1, a2, a3⟩ := r2 d hd
        exact ⟨a1, a2, i1 _ _ a3⟩
      · obtain ⟨a1, a2, a3⟩ := i2 x hx d hd
        exact ⟨a1, fun hm => a2 (r1 _ _ hm), a3⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact r3
      · exact i3 x hx
    · obtain ⟨-, -, a3⟩ := r2 d hd
      obtain ⟨-, b2, -⟩ := i2 y hy d' hd'
      rw [e, he] at a3
      exact b2 a3

/-- The marks at the start: as many as the part has places, all unset. -/
def marks0 (tl : HTailF2) : Array (Array Bool) := tl.tabLen.map fun n => Array.replicate n false

theorem marksOf_marks0 (tl : HTailF2) (q : Nat) : marksOf (marks0 tl) q = tl.tabLen.getD q 0 := by
  unfold marksOf marks0
  by_cases hq : q < tl.tabLen.size
  · simp [Array.getD, hq]
  · simp [Array.getD, hq]

/-- After cover_of_marks. -/
theorem cover_of_marksRun (tl1 : HTailF2) (funs : Array HFun) (rd' : Array (Array Bool))
    (hr : MarksRun tl1 (readsList tl1 funs) (marks0 tl1) rd')
    (hall : (rd'.all fun a => a.all id) = true) (p i : Nat) (hi : i < tl1.tabLen.getD p 0) :
    ∃ x ∈ readsList tl1 funs, p = x.1.tree / 2 ∧ ∃ d, d < (tl1.mats.getD x.1.mat {}).k ∧
      posOf tl1 x.1 x.2 d = tl1.tabFirst.getD p 0 + i := by
  have hs : marksOf rd' p = tl1.tabLen.getD p 0 :=
    (marksRun_sizes tl1 _ _ _ hr p).trans (marksOf_marks0 tl1 p)
  have hset : markAt rd' p i := by
    unfold markAt
    unfold marksOf at hs
    have hlt : i < (rd'.getD p #[]).size := by omega
    have hp : p < rd'.size := by
      by_contra hge
      have : rd'.getD p #[] = #[] := by simp [Array.getD, hge]
      rw [this] at hlt
      simp at hlt
    have hmem : rd'.getD p #[] ∈ rd' := by
      rw [getD_lt _ _ _ hp]
      exact Array.getElem_mem hp
    have ha := (Array.all_eq_true_iff_forall_mem.1 hall) _ hmem
    have hb := (Array.all_eq_true_iff_forall_mem.1 ha) _ (Array.getElem_mem hlt)
    rw [getD_lt _ _ _ hlt]
    exact hb
  rcases marksRun_cover tl1 _ _ _ hr p i hset with h1 | h1
  · exfalso
    unfold markAt marks0 at h1
    by_cases hq : p < tl1.tabLen.size
    · by_cases hi2 : i < tl1.tabLen[p]
      · simp [Array.getD, hq, hi2] at h1
      · simp [Array.getD, hq, hi2] at h1
    · simp [Array.getD, hq] at h1
  · exact h1

/-- A read of the list is on U1 or on U3. -/
theorem tree_of_mem (tl : HTailF2) (funs : Array HFun) (x : HFun × Nat)
    (hx : x ∈ readsList tl funs) : x.1.tree = 0 ∨ x.1.tree = 2 := by
  obtain ⟨Fn, sg⟩ := x
  exact ((OnBytes.Tie.Pv.Tail.Port.mem_readsList tl funs Fn sg).1 hx).2.2.1

/-! ## The text -/

/-- One read of the text, as far as its vector and its marks go. -/
def stepME (tl : HTailF2) (x : HFun × Nat) (b : MProd Nat (Array (Array Bool))) (_ : St)
    (b1 : MProd Nat (Array (Array Bool))) (_ : St) : Prop :=
  (tl.ix.U.getD x.1.tree none).isSome = true ∧ tl.markRead x.1 x.2 b.snd = some b1.snd

theorem marksRun_of_fold (tl : HTailF2) :
    ∀ (l : List (HFun × Nat)) (b : MProd Nat (Array (Array Bool))) (s : St)
      (b' : MProd Nat (Array (Array Bool))) (s' : St),
      RunFoldE (stepME tl) l b s b' s' → MarksRun tl l b.snd b'.snd
  | [], b, _, b', _, h => by
    obtain ⟨rfl, -⟩ := h
    exact rfl
  | a :: l, b, s, b', s', h => by
    obtain ⟨b1, s1, ⟨hs, hm⟩, hr⟩ := h
    exact ⟨b1.snd, hs, hm, marksRun_of_fold tl l b1 s1 b' s' hr⟩

/-- The text behind the four first claims, as far as the marks go. After objectsF_marks. -/
theorem eqTail_marks (before : Nat) (tlb tl' : HTailF2) (funs : Array HFun)
    (front : Nat) (s s' : St) (h : eqTail before tlb funs front s = .ok (tl', s')) :
    ∃ (tl1 : HTailF2) (rd' : Array (Array Bool)) (t1 t2 : Array Nat) (t3 g1 g3 : Nat),
      eqWeights tlb front s = .ok (tl1, s) ∧
      tl' = { tl1 with tieObj := t1, tiesOn := t2, nX4Laid := t3 } ∧
      MarksRun tl1 (readsList tl1 funs) (marks0 tl1) rd' ∧
      (rd'.all fun a => a.all id) = true ∧
      tl1.tablesTile funs 0 = some g1 ∧ tl1.tablesTile funs 2 = some g3 := by
  unfold eqTail at h
  obtain ⟨n0, t0, h0, k0⟩ := (eq_bind_ok _ _ _ _ _).1 h
  obtain ⟨en0, et0⟩ := eq_claims_ok h0
  rw [en0, et0] at k0
  obtain ⟨u1, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 k0
  obtain ⟨b4, et1⟩ := eq_must_ok h1
  rw [et1] at k1
  obtain ⟨tl1, t2, hW, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
  have eW : t2 = s := by
    unfold eqWeights at hW
    obtain ⟨x3, t3, g1, g2⟩ := (eq_bind_ok _ _ _ _ _).1 hW
    rw [(eq_ask_ok g1).2] at g2
    exact (eq_get_ok g2).2
  rw [eW] at hW k2
  obtain ⟨sz, t3, h3, k3⟩ := (eq_bind_ok _ _ _ _ _).1 k2
  rw [(eq_ask_ok h3).2] at k3
  obtain ⟨bT, sT, hT, k4⟩ := (eq_bind_ok _ _ _ _ _).1 k3
  obtain ⟨bR, sR, hR, k5⟩ := (eq_bind_ok _ _ _ _ _).1 k4
  obtain ⟨u6, t6, h6, k6⟩ := (eq_bind_ok _ _ _ _ _).1 k5
  rw [(eq_must_ok h6).2] at k6
  obtain ⟨u7, t7, h7, k7⟩ := (eq_bind_ok _ _ _ _ _).1 k6
  rw [(eq_must_ok h7).2] at k7
  obtain ⟨g1, t8, h8, k8⟩ := (eq_bind_ok _ _ _ _ _).1 k7
  rw [(eq_get_ok h8).2] at k8
  obtain ⟨g3, t9, h9, k9⟩ := (eq_bind_ok _ _ _ _ _).1 k8
  rw [(eq_get_ok h9).2] at k9
  obtain ⟨kinds, t10, h10, k10⟩ := (eq_bind_ok _ _ _ _ _).1 k9
  rw [(eq_ask_ok h10).2] at k10
  obtain ⟨u11, t11, h11, k11⟩ := (eq_bind_ok _ _ _ _ _).1 k10
  rw [(eq_must_ok h11).2] at k11
  obtain ⟨u12, t12, h12, k12⟩ := (eq_bind_ok _ _ _ _ _).1 k11
  rw [(eq_must_ok h12).2] at k12
  obtain ⟨u13, t13, h13, k13⟩ := (eq_bind_ok _ _ _ _ _).1 k12
  rw [(eq_must_ok h13).2] at k13
  obtain ⟨etl, es'⟩ := (eq_pure_ok _ _ _ _ _).1 k13
  -- the reads: four loops, flattened
  have rR := forInE_inv front _
    (fun mu => RunFoldE (fun un => RunFoldE (fun (Fn : HFun) => RunFoldE (stepME tl1)
      (segsOf tl1 mu un Fn)) funs.toList) [0, 2])
    (by
      intro mu b s r s1 hb
      obtain ⟨b2, x1, c1, d1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
      obtain ⟨u', x2, c2, d2⟩ := (eq_bind_ok _ _ _ _ _).1 d1
      rw [((eq_pure_ok _ _ _ _ _).1 c2).2] at d2
      obtain ⟨er, ex⟩ := (eq_pure_ok _ _ _ _ _).1 d2
      rw [ex]
      refine ⟨_, er, ?_⟩
      refine forInE_inv front _ _ ?_ _ _ _ _ _ c1
      intro un b s r s1 hb
      obtain ⟨b3, y1, c3, d3⟩ := (eq_bind_ok _ _ _ _ _).1 hb
      obtain ⟨u'', y2, c4, d4⟩ := (eq_bind_ok _ _ _ _ _).1 d3
      rw [((eq_pure_ok _ _ _ _ _).1 c4).2] at d4
      obtain ⟨er', ex'⟩ := (eq_pure_ok _ _ _ _ _).1 d4
      rw [ex']
      refine ⟨_, er', ?_⟩
      refine forInE_inv_array front _ _ ?_ _ _ _ _ _ c3
      intro Fn b s r s1 hb
      by_cases hc : (Fn.mat == mu && Fn.tree == un) = true
      · rw [if_pos hc] at hb
        obtain ⟨v1, z1, e1, f1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
        obtain ⟨hsome, ez1⟩ := eq_must_ok e1
        rw [ez1] at f1
        obtain ⟨v2, z2, e2, f2⟩ := (eq_bind_ok _ _ _ _ _).1 f1
        rw [(eq_must_ok e2).2] at f2
        obtain ⟨b4', z3, e3, f3⟩ := (eq_bind_ok _ _ _ _ _).1 f2
        obtain ⟨v4, z4, e4, f4⟩ := (eq_bind_ok _ _ _ _ _).1 f3
        rw [((eq_pure_ok _ _ _ _ _).1 e4).2] at f4
        obtain ⟨er2, ex2⟩ := (eq_pure_ok _ _ _ _ _).1 f4
        rw [ex2]
        have hc' := hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc'
        have hU : (tl1.ix.U.getD Fn.tree none).isSome = true := by
          rw [hc'.2]
          exact hsome
        refine ⟨_, er2, ?_⟩
        rw [segsOf, if_pos hc]
        apply runFoldE_map
        refine forInE_inv front _ _ ?_ _ _ _ _ _ e3
        intro sg b s r s1 hb
        obtain ⟨rd, w1, p1, q1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
        obtain ⟨hmr, ew1⟩ := eq_get_ok p1
        rw [ew1] at q1
        obtain ⟨v5, w2, p2, q2⟩ := (eq_bind_ok _ _ _ _ _).1 q1
        obtain ⟨v6, w3, p3, q3⟩ := (eq_bind_ok _ _ _ _ _).1 q2
        rw [((eq_pure_ok _ _ _ _ _).1 p3).2] at q3
        obtain ⟨er3, ex3⟩ := (eq_pure_ok _ _ _ _ _).1 q3
        rw [ex3]
        exact ⟨_, er3, hU, hmr⟩
      · rw [if_neg hc] at hb
        obtain ⟨v1, z1, e1, f1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
        rw [((eq_pure_ok _ _ _ _ _).1 e1).2] at f1
        obtain ⟨er2, ex2⟩ := (eq_pure_ok _ _ _ _ _).1 f1
        rw [ex2]
        refine ⟨_, er2, ?_⟩
        rw [segsOf, if_neg hc]
        exact ⟨rfl, rfl⟩) _ _ _ _ _ hR
  have s1 := runFoldE_mono _
    (fun mu => RunFoldE (fun un => RunFoldE (stepME tl1)
      (funs.toList.flatMap (segsOf tl1 mu un))) [0, 2])
    (fun mu _ _ _ _ h2 => runFoldE_mono _
      (fun un => RunFoldE (stepME tl1) (funs.toList.flatMap (segsOf tl1 mu un)))
      (fun un _ _ _ _ h3 => runFoldE_flat (stepME tl1) (segsOf tl1 mu un) _ _ _ _ _ h3)
      _ _ _ _ _ h2) _ _ _ _ _ rR
  have s2 := runFoldE_mono _
    (fun mu => RunFoldE (stepME tl1)
      ([0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl1 mu un)))
    (fun mu _ _ _ _ h2 => runFoldE_flat (stepME tl1)
      (fun un => funs.toList.flatMap (segsOf tl1 mu un)) _ _ _ _ _ h2) _ _ _ _ _ s1
  have fP := runFoldE_flat (stepME tl1)
    (fun mu => [0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl1 mu un)) _ _ _ _ _ s2
  exact ⟨tl1, _, _, _, _, g1, g3, hW, etl, marksRun_of_fold tl1 _ _ _ _ _ fP, (eq_must_ok h7).1,
    (eq_get_ok h8).1, (eq_get_ok h9).1⟩

/-- A yes of "K8.equations", cut at eqKeys, eqCounts and the tail. -/
theorem eq_parts {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    ∃ (before : Nat) (tla tlb : HTailF2) (s1 s2 : St) (arr : Array Claim),
      eqKeys tl front (F, #[]) = .ok (tla, s1) ∧ eqCounts tla front s1 = .ok (tlb, s2) ∧
      eqTail before tlb funs front s2 = .ok (tl', (F1, arr)) ∧ arr.toList = cls := by
  unfold equations at h
  cases e : eqAll tl funs front (F, #[]) with
  | error x => rw [e] at h; cases h
  | ok x =>
    rw [e] at h
    obtain ⟨tlx, Fx, arr⟩ := x
    have h' := Except.ok.inj h
    obtain rfl : tlx = tl' := congrArg Prod.fst h'
    obtain rfl : Fx = F1 := congrArg (fun y => y.2.1) h'
    have hcl : arr.toList = cls := congrArg (fun y => y.2.2) h'
    rw [eqAll_split] at e
    obtain ⟨u1, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 e
    rw [(eq_must_ok h1).2] at k1
    obtain ⟨u2, t2, h2, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
    rw [(eq_must_ok h2).2] at k2
    obtain ⟨z, t3, h3, k3⟩ := (eq_bind_ok _ _ _ _ _).1 k2
    rw [(eq_ask_ok h3).2] at k3
    obtain ⟨u4, t4, h4, k4⟩ := (eq_bind_ok _ _ _ _ _).1 k3
    rw [(eq_test_ok h4).2] at k4
    obtain ⟨g', t5, h5, k5⟩ := (eq_bind_ok _ _ _ _ _).1 k4
    rw [(eq_get_ok h5).2] at k5
    obtain ⟨u6, t6, h6, k6⟩ := (eq_bind_ok _ _ _ _ _).1 k5
    rw [(eq_must_ok h6).2] at k6
    unfold eqRest at k6
    obtain ⟨before, t7, h7, k7⟩ := (eq_bind_ok _ _ _ _ _).1 k6
    rw [(eq_claims_ok h7).2] at k7
    obtain ⟨tla, s1, h8, k8⟩ := (eq_bind_ok _ _ _ _ _).1 k7
    obtain ⟨tlb, s2, h9, k9⟩ := (eq_bind_ok _ _ _ _ _).1 k8
    exact ⟨before, tla, tlb, s1, s2, arr, h8, h9, k9, hcl⟩

/-- A yes of "K8.equations", as far as the marks go. -/
theorem eq_marks {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    ∃ (tl1 : HTailF2) (rd' : Array (Array Bool)) (t1 t2 : Array Nat) (t3 g1 g3 : Nat),
      tl' = { tl1 with tieObj := t1, tiesOn := t2, nX4Laid := t3 } ∧
      MarksRun tl1 (readsList tl1 funs) (marks0 tl1) rd' ∧
      (rd'.all fun a => a.all id) = true ∧
      tl1.tablesTile funs 0 = some g1 ∧ tl1.tablesTile funs 2 = some g3 := by
  obtain ⟨before, tla, tlb, s1, s2, arr, -, -, k9, -⟩ := eq_parts h
  obtain ⟨tl1, rd', t1, t2, t3, g1, g3, -, etl, hr, hall, a0, a2⟩ :=
    eqTail_marks before tlb tl' funs front s2 (F1, arr) k9
  exact ⟨tl1, rd', t1, t2, t3, g1, g3, etl, hr, hall, a0, a2⟩

/-- What the returned record has in common with the record that was handed in: every function f of
the record that does not read the fields that the text sets. -/
theorem eq_same {α : Sort _} (f : HTailF2 → α) {front : Nat} {tl tl' : HTailF2}
    {funs : Array HFun} {F F1 : Fork} {cls : List Claim}
    (h : equations front tl funs F = .ok (tl', F1, cls))
    (r1 : ∀ (t : HTailF2) (x : Option Nat), f { t with joinObj9 := x } = f t)
    (r2 : ∀ (t : HTailF2) (x : E), f { t with bitFactor9 := x } = f t)
    (r3 : ∀ (t u : HTailF2),
      f { t with
          vt := u.vt, vp := u.vp, eqFirst := u.eqFirst, rowX := u.rowX, loX := u.loX,
          gamX := u.gamX, gamV := u.gamV, foldTakenF := u.foldTakenF } = f t)
    (r4 : ∀ (t : HTailF2) (x y : Array Nat) (z : Nat),
      f { t with tieObj := x, tiesOn := y, nX4Laid := z } = f t) : f tl' = f tl := by
  obtain ⟨before, tla, tlb, s1, s2, arr, h8, h9, k9, -⟩ := eq_parts h
  obtain ⟨tl1, rd', t1, t2, t3, g1, g3, hW, etl, -⟩ :=
    eqTail_marks before tlb tl' funs front s2 (F1, arr) k9
  obtain ⟨-, e1, -⟩ := eqWeights_spec tlb tl1 front s2 s2 hW
  exact carry4 f (eqKeys_spec tl tla _ _ _ h8) (r1 _ _) (eqCounts_spec tla tlb _ _ _ h9) (r2 _ _)
    e1 (r3 _ _) etl (r4 _ _ _ _)

/-! ## The rows -/

/-- **Every place of the part of a vector that holds tables is named by a read.** After
objectsF_cover. -/
def K08Cover : Prop :=
  ∀ (front : Nat) (tl tl' : HTailF2) (funs : Array HFun) (F F1 : Fork) (cls : List Claim),
    equations front tl funs F = .ok (tl', F1, cls) →
    ∀ p i : Nat, i < tl'.tabLen.getD p 0 →
    ∃ x ∈ readsList tl' funs, p = x.1.tree / 2 ∧ ∃ d, d < (tl'.mats.getD x.1.mat {}).k ∧
      posOf tl' x.1 x.2 d = tl'.tabFirst.getD p 0 + i

theorem eq_cover : K08Cover := by
  intro front tl tl' funs F F1 cls h p i hi
  obtain ⟨tl1, rd', t1, t2, t3, g1, g3, rfl, hr, hall, -, -⟩ := eq_marks h
  exact cover_of_marksRun tl1 funs rd' hr hall p i hi

/-- **Where the part of U3 begins at 0 and has the vector's length: every place below the length is
named by a read on U3.** After objectsF_coverU3. -/
def K08CoverU3 : Prop :=
  ∀ (front : Nat) (tl tl' : HTailF2) (funs : Array HFun) (F F1 : Fork) (cls : List Claim),
    equations front tl funs F = .ok (tl', F1, cls) →
    tl'.tabFirst.getD 1 0 = 0 → tl'.tabLen.getD 1 0 = tl'.nUF.getD 2 0 →
    ∀ pos : Nat, pos < tl'.nUF.getD 2 0 →
    ∃ x ∈ readsList tl' funs, x.1.tree = 2 ∧ ∃ d, d < (tl'.mats.getD x.1.mat {}).k ∧
      posOf tl' x.1 x.2 d = pos

theorem eq_coverU3 : K08CoverU3 := by
  intro front tl tl' funs F F1 cls h hf hl pos hp
  obtain ⟨x, hx, e, d, d1, d2⟩ := eq_cover front tl tl' funs F F1 cls h 1 pos (by omega)
  refine ⟨x, hx, ?_, d, d1, by omega⟩
  rcases tree_of_mem tl' funs x hx with e0 | e2
  · rw [e0] at e
    omega
  · exact e2

/-- **For every read the vector is there, and every place that the read names lies below the length
that the record holds for the vector.** After objectsF_reads. -/
def K08Reads : Prop :=
  ∀ (front : Nat) (tl tl' : HTailF2) (funs : Array HFun) (F F1 : Fork) (cls : List Claim),
    equations front tl funs F = .ok (tl', F1, cls) →
    ∀ x ∈ readsList tl' funs, (tl'.ix.U.getD x.1.tree none).isSome = true ∧
      ∀ d, d < (tl'.mats.getD x.1.mat {}).k → posOf tl' x.1 x.2 d < tl'.nUF.getD x.1.tree 0

theorem reads_of_marksRun (tl1 : HTailF2) (funs : Array HFun) (rd' : Array (Array Bool))
    (g1 g3 : Nat) (hr : MarksRun tl1 (readsList tl1 funs) (marks0 tl1) rd')
    (a0 : tl1.tablesTile funs 0 = some g1) (a2 : tl1.tablesTile funs 2 = some g3) :
    ∀ x ∈ readsList tl1 funs, (tl1.ix.U.getD x.1.tree none).isSome = true ∧
      ∀ d, d < (tl1.mats.getD x.1.mat {}).k → posOf tl1 x.1 x.2 d < tl1.nUF.getD x.1.tree 0 := by
  intro x hx
  obtain ⟨hs, hp⟩ := marksRun_reads tl1 (fun p => tl1.tabLen.getD p 0) _ _ _ hr
    (marksOf_marks0 tl1) x hx
  refine ⟨hs, fun d hd => ?_⟩
  have hlt := hp d hd
  have hle : tl1.tabFirst.getD (x.1.tree / 2) 0 + tl1.tabLen.getD (x.1.tree / 2) 0 ≤
      tl1.nUF.getD x.1.tree 0 := by
    rcases tree_of_mem tl1 funs x hx with e | e
    · rw [e] at hs ⊢
      exact tablesTile_le tl1 funs 0 _ a0 hs
    · rw [e] at hs ⊢
      exact tablesTile_le tl1 funs 2 _ a2 hs
  exact Nat.lt_of_lt_of_le hlt hle

theorem eq_reads : K08Reads := by
  intro front tl tl' funs F F1 cls h
  obtain ⟨tl1, rd', t1, t2, t3, g1, g3, rfl, hr, -, a0, a2⟩ := eq_marks h
  exact reads_of_marksRun tl1 funs rd' g1 g3 hr a0 a2

/-- **The list of reads is pairwise apart, and each read's places at two columns differ.** After
objectsF_apart. -/
def K08Apart : Prop :=
  ∀ (front : Nat) (tl tl' : HTailF2) (funs : Array HFun) (F F1 : Fork) (cls : List Claim),
    equations front tl funs F = .ok (tl', F1, cls) →
    (readsList tl' funs).Pairwise (PlacesApart tl') ∧
      ∀ x ∈ readsList tl' funs, ∀ d d', d < d' → d' < (tl'.mats.getD x.1.mat {}).k →
        posOf tl' x.1 x.2 d ≠ posOf tl' x.1 x.2 d'

theorem eq_apart : K08Apart := by
  intro front tl tl' funs F F1 cls h
  obtain ⟨tl1, rd', t1, t2, t3, g1, g3, rfl, hr, -, -, -⟩ := eq_marks h
  obtain ⟨-, -, i3, i4⟩ := marksRun_once tl1 _ _ _ hr
  exact ⟨i4, i3⟩

/-- Two reads of the list and two columns with one place, on one part of the marks: the same read and
the same column. After objectsF_once. -/
theorem eq_once {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) (x y : HFun × Nat)
    (hx : x ∈ readsList tl' funs) (hy : y ∈ readsList tl' funs)
    (e : x.1.tree / 2 = y.1.tree / 2) (d d' : Nat) (hd : d < (tl'.mats.getD x.1.mat {}).k)
    (hd' : d' < (tl'.mats.getD y.1.mat {}).k)
    (he : posOf tl' x.1 x.2 d = posOf tl' y.1 y.2 d') : x = y ∧ d = d' := by
  obtain ⟨hp, hc⟩ := eq_apart front tl tl' funs F F1 cls h
  have hxy : x = y := by
    by_contra hne
    exact hp.forall (fun _ _ hs => hs.symm) hx hy hne e d hd d' hd' he
  subst hxy
  refine ⟨rfl, ?_⟩
  rcases Nat.lt_trichotomy d d' with h1 | h1 | h1
  · exact absurd he (hc x hx d d' h1 hd')
  · exact h1
  · exact absurd he.symm (hc x hx d' d h1 hd)

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_cover
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_coverU3
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_reads
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_apart
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_once
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_same
