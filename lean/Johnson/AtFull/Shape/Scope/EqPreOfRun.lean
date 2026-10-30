-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/EqPreOfRun.lean: A YES OF THE RUN "K8.equations" AT A STATE GIVES THE RUN's THREE TESTS ON
VALUES AT THAT STATE (EqPre): the tables are held and the window of the smallness test is clear, which the list tests
first of all; and no column of a matrix with a read has the weight 0 at the batching element, which each read tests
of its own columns (the test "internal-f-table-read" at noneIsZero, Equations.lean's eqRead; testAs refuses here: ForkM.lean). So where
the run has returned none of the three hangs on a coin: the element can make the run refuse, not make it return
with a test failed.

  readEnts_live      a true flag behind readEnts: no weight of the columns read is 0.
  LiveAt, read_live  what one read tests of its columns.
  eqTail_live        the text's reads, after eqTail_marks (EquationsCover.lean).
  eq_live            LiveCols from a yes of the list.
  eq_heads           the first two tests from a yes of the list.
  **eqPre_of_run**   EqPre at the state in front, from a yes of the run.

Limits. One direction, from a yes. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.TailClaims.EquationsCover
import Johnson.Desc.K8.Honest.EqAllRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.Tie.Pv.Tail.Port
open VerifiableInference.Desc.First.K8.Honest (LiveCols EqPre)

/-- A true flag behind the walk over the columns: the flag was true in front, and no weight read is 0. -/
theorem readEnts_live (tl : HTailF2) (Fn : HFun) (sg tU cols : Nat) (minus : E) (gc : Array E) :
    ∀ (count c : Nat) (ents ents' : Array Ent) (b : Bool),
      tl.readEnts Fn sg tU cols minus gc count c ents b = some (ents', true) →
      b = true ∧ ∀ i, c ≤ i → i < c + count → isZeroE (gc.getD i zeroE) = false
  | 0, c, ents, ents', b, h => by
    have e : some (ents, b) = some (ents', true) := h
    have e' := Option.some.inj e
    exact ⟨congrArg Prod.snd e', fun i h1 h2 => by omega⟩
  | count + 1, c, ents, ents', b, h => by
    unfold HTailF2.readEnts at h
    cases hp : tl.tabAt Fn c sg with
    | none =>
      rw [hp] at h
      cases h
    | some pos =>
      rw [hp] at h
      obtain ⟨h1, h2⟩ := readEnts_live tl Fn sg tU cols minus gc count (c + 1) _ ents' _ h
      rw [Bool.and_eq_true] at h1
      have hz : isZeroE (gc.getD c zeroE) = false := by
        have := h1.2
        simpa using this
      refine ⟨h1.1, fun i a1 a2 => ?_⟩
      by_cases e : i = c
      · rw [e]
        exact hz
      · exact h2 i (by omega) (by omega)

/-- What one read tests: no column of its matrix has the weight 0. -/
def LiveAt (tl : HTailF2) (x : HFun × Nat) : Prop :=
  ∀ c, c < (tl.mats.getD x.1.mat {}).k → isZeroE ((tl.gamV.getD x.1.mat #[]).getD c zeroE) = false

theorem read_live {tl : HTailF2} {Fn : HFun} {sg laid : Nat} {sums : E} {front : Nat} {s s1 : St}
    {r : Unit} (h : eqRead tl Fn sg laid sums front s = .ok (r, s1)) : LiveAt tl (Fn, sg) := by
  unfold eqRead at h
  obtain ⟨tU, x1, a1, b1⟩ := (eq_bind_ok _ _ _ _ _).1 h
  rw [(eq_get_ok a1).2] at b1
  obtain ⟨cols, x2, a2, b2⟩ := (eq_bind_ok _ _ _ _ _).1 b1
  rw [(eq_ask_ok a2).2] at b2
  obtain ⟨u3, x3, a3, b3⟩ := (eq_bind_ok _ _ _ _ _).1 b2
  rw [(eq_must_ok a3).2] at b3
  obtain ⟨pr, x4, a4, b4⟩ := (eq_bind_ok _ _ _ _ _).1 b3
  have eE := (eq_get_ok a4).1
  rw [(eq_get_ok a4).2] at b4
  obtain ⟨ents, nz⟩ := pr
  obtain ⟨u5, x5, a5, b5⟩ := (eq_bind_ok _ _ _ _ _).1 b4
  have hz : nz = true := (eq_test_ok a5).1
  subst hz
  intro c hc
  have hc' : c < (tl.mats.getD Fn.mat {}).k := hc
  exact (readEnts_live tl Fn sg tU cols _ _ _ 0 _ ents _ eE).2 c (Nat.zero_le _) (by omega)

/-- One read of the text, as far as its columns go. -/
def stepLE (tl : HTailF2) (x : HFun × Nat) (_ : MProd Nat (Array (Array Bool))) (_ : St)
    (_ : MProd Nat (Array (Array Bool))) (_ : St) : Prop := LiveAt tl x

theorem live_of_fold (tl : HTailF2) :
    ∀ (l : List (HFun × Nat)) (b : MProd Nat (Array (Array Bool))) (s : St)
      (b' : MProd Nat (Array (Array Bool))) (s' : St),
      RunFoldE (stepLE tl) l b s b' s' → ∀ x ∈ l, LiveAt tl x
  | [], _, _, _, _, _, x, hx => by cases hx
  | a :: l, b, s, b', s', h, x, hx => by
    obtain ⟨b1, s1, hs, hr⟩ := h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hs
    · exact live_of_fold tl l b1 s1 b' s' hr x hx

/-- The text behind the four first claims, as far as the columns go. After eqTail_marks. -/
theorem eqTail_live (before : Nat) (tlb tl' : HTailF2) (funs : Array HFun)
    (front : Nat) (s s' : St) (h : eqTail before tlb funs front s = .ok (tl', s')) :
    ∃ tl1 : HTailF2, eqWeights tlb front s = .ok (tl1, s) ∧
      ∀ x ∈ readsList tl1 funs, LiveAt tl1 x := by
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
    (fun mu => RunFoldE (fun un => RunFoldE (fun (Fn : HFun) => RunFoldE (stepLE tl1)
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
        exact ⟨_, er3, read_live p2⟩
      · rw [if_neg hc] at hb
        obtain ⟨v1, z1, e1, f1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
        rw [((eq_pure_ok _ _ _ _ _).1 e1).2] at f1
        obtain ⟨er2, ex2⟩ := (eq_pure_ok _ _ _ _ _).1 f1
        rw [ex2]
        refine ⟨_, er2, ?_⟩
        rw [segsOf, if_neg hc]
        exact ⟨rfl, rfl⟩) _ _ _ _ _ hR
  have s1 := runFoldE_mono _
    (fun mu => RunFoldE (fun un => RunFoldE (stepLE tl1)
      (funs.toList.flatMap (segsOf tl1 mu un))) [0, 2])
    (fun mu _ _ _ _ h2 => runFoldE_mono _
      (fun un => RunFoldE (stepLE tl1) (funs.toList.flatMap (segsOf tl1 mu un)))
      (fun un _ _ _ _ h3 => runFoldE_flat (stepLE tl1) (segsOf tl1 mu un) _ _ _ _ _ h3)
      _ _ _ _ _ h2) _ _ _ _ _ rR
  have s2 := runFoldE_mono _
    (fun mu => RunFoldE (stepLE tl1)
      ([0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl1 mu un)))
    (fun mu _ _ _ _ h2 => runFoldE_flat (stepLE tl1)
      (fun un => funs.toList.flatMap (segsOf tl1 mu un)) _ _ _ _ _ h2) _ _ _ _ _ s1
  have fP := runFoldE_flat (stepLE tl1)
    (fun mu => [0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl1 mu un)) _ _ _ _ _ s2
  exact ⟨tl1, hW, live_of_fold tl1 _ _ _ _ _ fP⟩

theorem getD_map_range {k c : Nat} (hc : c < k) (f : Nat → E) (d : E) :
    ((Array.range k).map f).getD c d = f c := by
  have hs : c < ((Array.range k).map f).size := by simpa using hc
  unfold Array.getD
  rw [dif_pos hs]
  simp

/-- **No column of a matrix with a read has the weight 0 at the batching element, from a yes of the list.** -/
theorem eq_live {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    LiveCols tl funs F.theta := by
  obtain ⟨before, tla, tlb, s1, s2, arr, h8, h9, k9, -⟩ := eq_parts h
  obtain ⟨tl1, hW, hl⟩ := eqTail_live before tlb tl' funs front s2 (F1, arr) k9
  obtain ⟨hP, e1, hgam⟩ := eqWeights_spec tlb tl1 front s2 s2 hW
  obtain ⟨o1, -, -⟩ := tame_keys tl _ _ _ _ h8
  obtain ⟨o2, -, -⟩ := tame_counts tla _ _ _ _ h9
  have eth : s2.1.theta = F.theta := (o1.trans o2).theta
  have ea := eqKeys_spec tl tla _ _ _ h8
  have eb := eqCounts_spec tla tlb _ _ _ h9
  have eNM : tl1.NM = tl.NM := by rw [e1, eb, ea]
  have eM : tl1.mats = tl.mats := by rw [e1, eb, ea]
  have eC : tl1.cfF = tl.cfF := by rw [e1, eb, ea]
  have eF : tl1.cfFirst = tl.cfFirst := by rw [e1, eb, ea]
  have eT : tl1.tau = tl.tau := by rw [e1, eb, ea]
  have eR : readsList tl1 funs = readsList tl funs := by
    unfold readsList segsOf
    rw [eNM, eM]
  intro x hx c hc
  have hx1 : x ∈ readsList tl1 funs := by rw [eR]; exact hx
  have hN : x.1.mat < tl1.NM := ((mem_readsList tl1 funs x.1 x.2).1 hx1).2.1
  have hc1 : c < (tl1.mats.getD x.1.mat {}).k := by rw [eM]; exact hc
  have hz := hl x hx1 c hc1
  rw [(hgam x.1.mat hN).2] at hz
  have e2 : (gamAt tl1 x.1.mat).getD c zeroE =
      foldColumn tl1.cfF ((tl1.cfFirst.getD x.1.mat 0 + c) * tl1.tau) tl1.tau tl1.vp := by
    unfold gamAt
    exact getD_map_range hc1 _ _
  rw [e2, hP.vp, eC, eF, eT, eth] at hz
  exact hz

/-- The first two tests, from a yes of the list. -/
theorem eq_heads {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    tl.funsHeld funs = true ∧ (F.LS.extract tl.slotA tl.slotB).all isZeroE = true := by
  unfold equations at h
  cases e : eqAll tl funs front (F, #[]) with
  | error x =>
    rw [e] at h
    cases h
  | ok x =>
    rw [eqAll_split] at e
    obtain ⟨u1, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 e
    rw [(eq_must_ok h1).2] at k1
    obtain ⟨u2, t2, h2, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
    have eh := (eq_must_ok h2).1
    rw [(eq_must_ok h2).2] at k2
    obtain ⟨z, t3, h3, k3⟩ := (eq_bind_ok _ _ _ _ _).1 k2
    have ea := (eq_ask_ok h3).1
    rw [(eq_ask_ok h3).2, (eq_must_ok h1).2] at *
    obtain ⟨u4, t4, h4, k4⟩ := (eq_bind_ok _ _ _ _ _).1 k3
    have et := (eq_test_ok h4).1
    obtain rfl : (F.LS.extract tl.slotA tl.slotB).all isZeroE = z := Option.some.inj ea
    exact ⟨eh, et⟩

/-- **A YES OF THE RUN "K8.equations" AT u: THE RUN's THREE TESTS ON VALUES HOLD AT u.** -/
theorem eqPre_of_run (p : K8.ParW) (run : Nat → S → Except String (List Claim × S))
    (hrun : ("K8.equations", run) ∈ (K8.whole p).claims) {n : Nat} {u u' : S} {cs : List Claim}
    (h : run n u = .ok (cs, u')) : EqPre u := by
  obtain ⟨q, tl', F1, hq, he, -⟩ := (sits_equations p run hrun n u u' cs).1 h
  intro q' hq'
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
  obtain ⟨a, b⟩ := eq_heads he
  exact ⟨a, b, eq_live he⟩

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_live
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_heads
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqPre_of_run
