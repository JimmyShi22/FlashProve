-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsForms.lean: the claims' half of the smallness test's law,
proved of the list's own text: the ties and reads of "K8.equations", added, are the batch at the
batching element of the list of single equations.

Definitions, statements and proofs. After OnBytes/Tie/Pv/Tail/EndClosed.lean (weightsF_spec),
EndLoopsB.lean (weightsF_gam, objectsF_fits_total), EndAll.lean (objectsF_ends), EndSame.lean,
EndSpread.lean (objectsF_spread) and EndForms.lean (objectsF_forms), which say the like of
`verify-on-bytes`'s routine objectsF. No routine of it is named here. USED OF THESE FILES, EACH ON
RECORDS AND PLAIN DATA ALONE: Powered and its laws, powersF_spec, foldSums_fold, foldSums_fold_gam,
gamAt, gamAt_congr, gamAt_val, gamSign, firstOf, tieClosed, readClosed, tieClosed_raw,
readClosed_raw, tieEnd, readEnd, RawRows, Fits, carry4, topOf, rowsTail, Rising, rising_rowsTail,
bounds_rowsTail, batch_rowsTail, batchOf, rowsForm, batch_rowsForm, fst_rowsForm, nodup_of_rising,
mem_readsList, sumFrom_congr, colsU_frame, Kept, colsU, uOf, posOf, tieTerm, readTerm, readsList,
sumFrom, Fits.of_same, Lay, Lay.cellAt, batchAt, TWhole.Form.gap (Cb/G6/Led.lean), Alg.symRows,
Fork.total; of the record the fields zzRowTies, zzRowReads, stepF among others.
Main names:
  eqWeights_spec, eqKeys_spec, eqCounts_spec: what these routines leave in the tail's record.
  closed_of_total, spread_of_total: the steps from the sum of brackets to the batch of single
    equations.
  **K08Claims** (a closed Prop), **k08_claims**.
Limits: one direction, from a yes. Fits and RawRows are premises. Totals at a reading. Of the first
four claims only their number and place. The list look, added in front, is any list: which claims the
lookup's own block lays there is the lookup's files' to show.

-/
import Johnson.Desc.First.TailClaims.EquationsTame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows Finset

/-! ## What three routines leave in the tail's record -/

theorem eqWeights_spec (tl tl1 : HTailF2) (front : Nat) (s s1 : St)
    (h : eqWeights tl front s = .ok (tl1, s1)) :
    Powered tl1 s.1.theta ∧
      tl1 = { tl with vt := tl1.vt, vp := tl1.vp, eqFirst := tl1.eqFirst, rowX := tl1.rowX,
                      loX := tl1.loX, gamX := tl1.gamX, gamV := tl1.gamV,
                      foldTakenF := tl1.foldTakenF } ∧
      ∀ mu, mu < tl1.NM →
        tl1.gamX.getD mu #[] = gamAt tl1 mu ∧ tl1.gamV.getD mu #[] = gamAt tl1 mu := by
  unfold eqWeights at h
  obtain ⟨tl2, t, g1, g2⟩ := (eq_bind_ok _ _ _ _ _).1 h
  have hp := (eq_ask_ok g1).1
  have hf := (eq_get_ok g2).1
  obtain ⟨hP, e2⟩ := powersF_spec tl tl2 s.1 hp
  have e1 := foldSums_fold _ _ _ hf
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    exact ⟨hP.vp, hP.vt, hP.rowX, hP.loX, hP.eqFirst, hP.shape⟩
  · rw [e1, e2]
  · obtain ⟨s1', s2', hall⟩ := foldSums_fold_gam (List.range tl2.NM)
      { tl2 with gamX := Array.replicate tl2.NM #[], gamV := Array.replicate tl2.NM #[] } tl1
      (hP.vt.trans hP.vp.symm) hf
    have eN : tl1.NM = tl2.NM := by rw [e1]
    intro mu hmu
    rw [eN] at hmu
    obtain ⟨ax, av⟩ := hall mu
      (by
        show mu < (Array.replicate tl2.NM (#[] : Array E)).size
        rw [Array.size_replicate]
        exact hmu)
      (by
        show mu < (Array.replicate tl2.NM (#[] : Array E)).size
        rw [Array.size_replicate]
        exact hmu)
    rw [gamAt_congr _ tl1 e1 mu]
    exact ⟨ax (Or.inl (List.mem_range.2 hmu)), av (Or.inl (List.mem_range.2 hmu))⟩

theorem eqKeys_spec (tl tl' : HTailF2) (front : Nat) (s s' : St)
    (h : eqKeys tl front s = .ok (tl', s')) : tl' = { tl with joinObj9 := tl'.joinObj9 } := by
  unfold eqKeys at h
  simp only [eq_bind_ok, eq_pure_ok] at h
  iterate 9 obtain ⟨_, _, _, h⟩ := h
  obtain ⟨rfl, _⟩ := h
  rfl

theorem eqCounts_spec (tl tl' : HTailF2) (front : Nat) (s s' : St)
    (h : eqCounts tl front s = .ok (tl', s')) : tl' = { tl with bitFactor9 := tl'.bitFactor9 } := by
  unfold eqCounts at h
  simp only [eq_bind_ok, eq_pure_ok] at h
  iterate 6 obtain ⟨_, _, _, h⟩ := h
  obtain ⟨rfl, _⟩ := h
  rfl

/-! ## From the sum of brackets to the batch of single equations -/

section
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-- After objectsF_fits_total. -/
theorem closed_of_total {tl1 tl' : HTailF2} {funs : Array HFun} {X4 G : Fork}
    (hP1 : Powered tl1 X4.theta)
    (hgam1 : ∀ mu, mu < tl1.NM →
      tl1.gamX.getD mu #[] = gamAt tl1 mu ∧ tl1.gamV.getD mu #[] = gamAt tl1 mu)
    (etl : tl' = { tl1 with tieObj := tl'.tieObj, tiesOn := tl'.tiesOn, nX4Laid := tl'.nX4Laid })
    (hk : Kept X4 G)
    (htot : G.total ρ W = X4.total ρ W + (((List.range tl1.NM).map (tieTerm ρ W tl1 X4)).sum
      + sumFrom (readTerm ρ W tl1 X4) 0 (readsList tl1 funs)))
    (hfit : ∀ mu, mu < tl'.NM → (tl'.shp.getD mu {}).m = (tl'.mats.getD mu {}).m ∧
      (tl'.shp.getD mu {}).k = (tl'.mats.getD mu {}).k) :
    G.total ρ W = X4.total ρ W
      + ((List.range tl'.NM).map fun mu =>
          ρ.val G.theta ^ (G.planClaimsF + firstOf tl' mu)
            * tieClosed W (ρ.val G.theta) (gamSign (ρ.val G.theta) tl') tl' mu).sum
      + sumFrom (fun q x =>
          ρ.val G.theta ^ (G.planClaimsF + (firstOf tl' tl'.NM + q * tl'.stepF))
            * readClosed ρ W (ρ.val G.theta) (gamSign (ρ.val G.theta) tl') tl' G x) 0
          (readsList tl' funs) := by
  have hP : Powered tl' G.theta := by
    rw [hk.theta, etl]
    exact ⟨hP1.vp, hP1.vt, hP1.rowX, hP1.loX, hP1.eqFirst, hP1.shape⟩
  have hgam : ∀ mu, mu < tl'.NM →
      tl'.gamX.getD mu #[] = gamAt tl' mu ∧ tl'.gamV.getD mu #[] = gamAt tl' mu := by
    rw [etl]
    exact hgam1
  have eNM : tl1.NM = tl'.NM := ((congrArg (fun t => t.NM) etl).trans rfl).symm
  have eL : readsList tl1 funs = readsList tl' funs :=
    ((congrArg (fun t => readsList t funs) etl).trans rfl).symm
  have eT : ∀ mu, tieTerm ρ W tl1 X4 mu = tieTerm ρ W tl' X4 mu := fun mu =>
    ((congrArg (fun t => tieTerm ρ W t X4 mu) etl).trans rfl).symm
  have eR : ∀ q x, readTerm ρ W tl1 X4 q x = readTerm ρ W tl' X4 q x := fun q x =>
    ((congrArg (fun t => readTerm ρ W t X4 q x) etl).trans rfl).symm
  rw [htot, eNM, eL, ← add_assoc]
  congr 1
  · congr 2
    apply List.map_congr_left
    intro mu hmu
    have hmu' : mu < tl'.NM := List.mem_range.1 hmu
    obtain ⟨fm, fk⟩ := hfit mu hmu'
    have eg : (tl'.gamX.getD mu #[]).size = (tl'.shp.getD mu {}).k := by
      rw [(hgam mu hmu').1, gamAt, Array.size_map, Array.size_range, fk]
    have hm : (tl'.shp.getD mu {}).m ≤ 3 * (tl'.shp.getD mu {}).mS := by
      have := (hP.shape mu hmu').2.2.2.2
      rw [fm]
      omega
    obtain ⟨wl, hwl⟩ := hP.tieLeft_some mu hmu'
    obtain ⟨wr, hwr⟩ := hP.tieRight_some mu hmu' eg
    rw [eT, tieTerm, ← hk.theta, ← hk.plan, hP.eqFirst_val mu (Nat.le_of_lt (hP.lt_shp mu hmu')),
      hP.tieBracket_closed ρ W mu hmu' (hP.lt_shp mu hmu') hm wl wr hwl hwr]
    unfold firstOf tieClosed gamSign
    congr 2
    apply Finset.sum_congr rfl
    intro p hp
    rw [(hgam mu hmu').1, gamAt_val ρ hP mu p (by rw [← fk]; exact Finset.mem_range.1 hp)]
  · apply sumFrom_congr
    intro q x hx
    obtain ⟨Fn, sg⟩ := x
    have hmat : Fn.mat < tl'.NM := ((mem_readsList tl' funs Fn sg).1 hx).2.1
    rw [eR, readTerm, ← hk.theta, ← hk.plan, hP.eqFirst_val tl'.NM hP.NM_le_shp,
      hP.readBracket_closed ρ W X4 (Fn, sg)]
    unfold firstOf readClosed gamSign
    simp only [colsU_frame G X4 hk.frame]
    congr 4
    apply Finset.sum_congr rfl
    intro d hd'
    rw [(hgam Fn.mat hmat).2, gamAt_val ρ hP Fn.mat d (Finset.mem_range.1 hd')]

/-- After objectsF_ends and objectsF_spread. -/
theorem spread_of_total {tl tla tlb tl1 tl' : HTailF2} {funs : Array HFun} {X4 G : Fork}
    (ea : tla = { tl with joinObj9 := tla.joinObj9 })
    (eb : tlb = { tla with bitFactor9 := tlb.bitFactor9 })
    (hP1 : Powered tl1 X4.theta)
    (e1 : tl1 = { tlb with vt := tl1.vt, vp := tl1.vp, eqFirst := tl1.eqFirst, rowX := tl1.rowX,
                           loX := tl1.loX, gamX := tl1.gamX, gamV := tl1.gamV,
                           foldTakenF := tl1.foldTakenF })
    (hgam1 : ∀ mu, mu < tl1.NM →
      tl1.gamX.getD mu #[] = gamAt tl1 mu ∧ tl1.gamV.getD mu #[] = gamAt tl1 mu)
    (etl : tl' = { tl1 with tieObj := tl'.tieObj, tiesOn := tl'.tiesOn, nX4Laid := tl'.nX4Laid })
    (hall : ∀ x ∈ readsList tl1 funs, x.1.phi.size = x.1.len)
    (hk : Kept X4 G)
    (htot : G.total ρ W = X4.total ρ W + (((List.range tl1.NM).map (tieTerm ρ W tl1 X4)).sum
      + sumFrom (readTerm ρ W tl1 X4) 0 (readsList tl1 funs)))
    (hfit : Fits tl) (A : Nat → Nat → Nat → K)
    (hV : RawRows W tl G funs (ρ.val G.theta) A) :
    Rising (rowsTail ρ tl funs G.planClaimsF) ∧
    (∀ r ∈ rowsTail ρ tl funs G.planClaimsF,
      G.planClaimsF ≤ r.1 ∧ r.1 < G.planClaimsF + topOf tl funs) ∧
    tl1.NM = tl.NM ∧ readsList tl1 funs = readsList tl funs ∧
    G.total ρ W = X4.total ρ W +
      batchOf (ρ.val G.theta) A (rowsTail ρ tl funs G.planClaimsF) := by
  have sRows : ∀ pc, rowsTail ρ tl' funs pc = rowsTail ρ tl funs pc := fun pc =>
    carry4 (fun t => rowsTail ρ t funs pc) ea rfl eb rfl e1 rfl etl rfl
  have sNM : tl'.NM = tl.NM := carry4 (fun t => t.NM) ea rfl eb rfl e1 rfl etl rfl
  have sShp : tl'.shp = tl.shp := carry4 (fun t => t.shp) ea rfl eb rfl e1 rfl etl rfl
  have sMats : tl'.mats = tl.mats := carry4 (fun t => t.mats) ea rfl eb rfl e1 rfl etl rfl
  have sReads : readsList tl' funs = readsList tl funs :=
    carry4 (fun t => readsList t funs) ea rfl eb rfl e1 rfl etl rfl
  have sReads1 : readsList tl' funs = readsList tl1 funs :=
    (congrArg (fun t => readsList t funs) etl).trans rfl
  have sNM1 : tl'.NM = tl1.NM := (congrArg (fun t => t.NM) etl).trans rfl
  have hV' : RawRows W tl' G funs (ρ.val G.theta) A :=
    ⟨(carry4 (fun t => ∀ c, W.entry t.ix.ZZ t.zzRowTies c =
          ∑ u ∈ range t.tau, ρ.val G.theta ^ u * A t.ix.ZZ u c)
        ea rfl eb rfl e1 rfl etl rfl).mpr hV.ties,
      (carry4 (fun t => ∀ c, W.entry t.ix.ZZ t.zzRowReads c =
          ∑ u ∈ range t.tau, ρ.val G.theta ^ u * A t.ix.ZZ u c)
        ea rfl eb rfl e1 rfl etl rfl).mpr hV.reads,
      (carry4 (fun t => ∀ mu, mu < t.NM → ∀ p, W.entry (t.gtTree.getD mu 0) 0 p =
          ∑ i' ∈ range (t.shp.getD mu {}).mS,
            ρ.val G.theta ^ (t.stepF * i') * A (t.gtTree.getD mu 0) i' p)
        ea rfl eb rfl e1 rfl etl rfl).mpr hV.syms,
      (carry4 (fun t => ∀ x ∈ readsList t funs, ∀ d, d < (t.mats.getD x.1.mat {}).k →
          W.entry (uOf t x.1) (posOf t x.1 x.2 d / colsU G (uOf t x.1))
            (posOf t x.1 x.2 d % colsU G (uOf t x.1)) = A (uOf t x.1) 0 (posOf t x.1 x.2 d))
        ea rfl eb rfl e1 rfl etl rfl).mpr hV.tabs⟩
  have hfit' : Fits tl' := hfit.of_same sNM sShp sMats
  have hsh' : ∀ mu, mu < tl'.NM →
      (tl'.shp.getD mu {}).mS = ((tl'.mats.getD mu {}).m + 2) / 3 := by
    rw [etl]
    exact fun mu hmu => (hP1.shape mu hmu).2.2.2.2
  have hphi : ∀ x ∈ readsList tl' funs, x.1.phi.size = x.1.len := by
    rw [sReads1]
    exact hall
  have hmS : ∀ mu, mu < tl.NM →
      (tl.shp.getD mu {}).mS = Alg.symRows (tl.shp.getD mu {}).m := by
    intro mu hmu
    have e := hsh' mu (by rw [sNM]; exact hmu)
    rw [sShp, sMats] at e
    rw [e, (hfit mu hmu).1]
    rfl
  have hc := closed_of_total ρ W hP1 hgam1 etl hk htot hfit'
  have hends : G.total ρ W = X4.total ρ W
      + ((List.range tl'.NM).map fun mu =>
          tieEnd A tl' (ρ.val G.theta) (G.planClaimsF + firstOf tl' mu) mu).sum
      + sumFrom (fun q x =>
          readEnd ρ A tl' (ρ.val G.theta)
            (G.planClaimsF + (firstOf tl' tl'.NM + q * tl'.stepF)) x) 0
          (readsList tl' funs) := by
    rw [hc]
    congr 1
    · congr 2
      apply List.map_congr_left
      intro mu hmu
      have hmu' : mu < tl'.NM := List.mem_range.1 hmu
      refine tieClosed_raw hV' _ mu hmu' ?_
      rw [hsh' mu hmu', (hfit' mu hmu').1]
      rfl
    · apply sumFrom_congr
      intro q x hx
      exact readClosed_raw ρ hV' _ x hx (hphi x hx)
  refine ⟨rising_rowsTail ρ tl funs _ hmS, bounds_rowsTail ρ tl funs _ hmS,
    sNM1.symm.trans sNM, sReads1.symm.trans sReads, ?_⟩
  rw [hends, add_assoc, ← batch_rowsTail, sRows]

end

/-! ## The row -/

theorem rawRows_cols {K : Type} [CommRing K] {W : World K} {tl : HTailF2} {G G' : Fork}
    {funs : Array HFun} {θ : K} {A : Nat → Nat → Nat → K} (h : RawRows W tl G funs θ A)
    (hc : ∀ t, colsU G' t = colsU G t) : RawRows W tl G' funs θ A :=
  ⟨h.ties, h.reads, h.syms, fun x hx d hd => by rw [hc]; exact h.tabs x hx d hd⟩

/-- **K08_law, the claims' half.** The list "K8.equations" is made at the record F and leaves F1; any
list look and then this list are added to F1 and leave G. Then: the list is four claims and then as
many as there are matrices and reads; no two exponents of the list of single equations
rowsForm are equal; each lies from the plan's number of claims on and at most topOf - 1 above it; and
behind the four the total grows by the gap, on the entries m, of the one form of that list at the
batching element. Premises: one coefficient for each slot; the shapes fit the matrices; the world
reads the four kinds of virtual rows off the cells of m. -/
def K08Claims : Prop :=
  ∀ (K : Type) [Field K] (J : Type) [Fintype J] (Y : Lay J) (ρ : Reading K) (W : World K)
    (m : J → K) (front : Nat) (tl tl' : HTailF2) (funs : Array HFun) (F F1 G : Fork)
    (look cls : List Claim),
    F.LS.size = F.ns → equations front tl funs F = .ok (tl', F1, cls) →
    addAll F1 (look ++ cls) = some G → Fits tl →
    RawRows W tl F1 funs (ρ.val F.theta) (fun t r c => Y.cellAt m t r c) →
    ((rowsForm Y ρ tl funs F.planClaimsF).map Prod.fst).Nodup ∧
    (∀ p ∈ rowsForm Y ρ tl funs F.planClaimsF,
      F.planClaimsF ≤ p.1 ∧ p.1 ≤ F.planClaimsF + topOf tl funs - 1) ∧
    ∃ (four rest : List Claim) (X X4 : Fork), cls = four ++ rest ∧ four.length = 4 ∧
      rest.length = tl.NM + (readsList tl funs).length ∧ addAll F1 look = some X ∧
      addAll X four = some X4 ∧ addAll X4 rest = some G ∧
      G.total ρ W = X4.total ρ W +
        (batchAt (ρ.val F.theta) (rowsForm Y ρ tl funs F.planClaimsF)).gap m

theorem k08_claims : K08Claims := by
  intro K _ J _ Y ρ W m front tl tl' funs F F1 G look cls hs h hadd hfit hV
  unfold equations at h
  cases e : eqAll tl funs front (F, #[]) with
  | error x => rw [e] at h; cases h
  | ok x =>
    rw [e] at h
    obtain ⟨tlx, Fx, arr⟩ := x
    have h' := Except.ok.inj h
    have htl : tlx = tl' := congrArg Prod.fst h'
    have hFx : Fx = F1 := congrArg (fun y => y.2.1) h'
    have hcl : arr.toList = cls := congrArg (fun y => y.2.2) h'
    rw [← hFx] at hadd hV
    rw [← hcl] at hadd
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
    obtain ⟨hbef, et7⟩ := eq_claims_ok h7
    rw [et7] at k7
    obtain ⟨tla, s1, h8, k8⟩ := (eq_bind_ok _ _ _ _ _).1 k7
    obtain ⟨tlb, s2, h9, k9⟩ := (eq_bind_ok _ _ _ _ _).1 k8
    obtain ⟨o1, n1, a1⟩ := tame_keys tl _ _ _ _ h8
    obtain ⟨o2, n2, a2⟩ := tame_counts tla _ _ _ _ h9
    -- a first look at the tail, for the list alone
    obtain ⟨tl1, hW, h44, hlaid, etl, hall, n3, e3, l3, _⟩ :=
      eqTail_total ρ W F before tlb tlx funs front s2 (Fx, arr) k9
    have hF2 : Fx = s2.1 := congrArg Prod.fst e3
    have harr : arr = s2.2 ++ n3.toArray := congrArg Prod.snd e3
    have hs2 : s2.2 = (n1 ++ n2).toArray := by
      rw [a2, a1]
      simp
    have hl : arr.toList = (n1 ++ n2) ++ n3 := by
      rw [harr, hs2]
      simp
    have hlen : (n1 ++ n2).length = 4 := by
      have q : front + (n1 ++ n2).length - (front + 0) = 4 := by
        rw [hbef, hs2] at h44
        exact h44
      omega
    rw [hl, addAll_append] at hadd
    obtain ⟨X, hX, hadd2⟩ := Option.bind_eq_some_iff.1 hadd
    rw [addAll_append] at hadd2
    obtain ⟨X4, hX4, hG⟩ := Option.bind_eq_some_iff.1 hadd2
    have os : OnlySide F Fx := by
      rw [hF2]
      exact o1.trans o2
    have sF : Fx.LS.size = Fx.ns := by
      rw [os.LS, os.ns]
      exact hs
    obtain ⟨oX, _, sX⟩ := addAll_keeps look Fx X sF hX
    obtain ⟨o4, _, s4⟩ := addAll_keeps (n1 ++ n2) X X4 sX hX4
    -- the tail again, against X4
    obtain ⟨tl1', hW', _, _, _, _, n3', e3', _, push⟩ :=
      eqTail_total ρ W X4 before tlb tlx funs front s2 (Fx, arr) k9
    have htl1 : tl1' = tl1 := congrArg Prod.fst (Except.ok.inj (hW'.symm.trans hW))
    have hn3 : n3' = n3 := by
      have q : s2.2 ++ n3'.toArray = s2.2 ++ n3.toArray :=
        (congrArg Prod.snd e3').symm.trans harr
      have q' := congrArg Array.toList q
      simpa using q'
    rw [htl1, hn3] at push
    have fr : Fr X4 s2.1 := by
      unfold Fr
      rw [← hF2]
      exact (o4.trees.trans oX.trees).symm
    obtain ⟨hk, _, htot⟩ := push fr X4 G ⟨rfl, rfl, s4, rfl⟩ hG
    obtain ⟨hP1, e1, hgam1⟩ := eqWeights_spec tlb tl1 front s2 s2 hW
    have th4 : X4.theta = F.theta := (o4.theta.trans oX.theta).trans os.theta
    have pl4 : X4.planClaimsF = F.planClaimsF := (o4.plan.trans oX.plan).trans os.plan
    have thG : G.theta = F.theta := hk.theta.trans th4
    have plG : G.planClaimsF = F.planClaimsF := hk.plan.trans pl4
    have hP1' : Powered tl1 X4.theta := by
      rw [th4, ← os.theta, hF2]
      exact hP1
    have hV' : RawRows W tl G funs (ρ.val G.theta) (fun t r c => Y.cellAt m t r c) := by
      rw [thG]
      exact rawRows_cols hV fun t =>
        colsU_frame G Fx ((hk.frame.trans o4.trees).trans oX.trees) t
    obtain ⟨hr, hb, eNM, eReads, ht⟩ := spread_of_total ρ W (eqKeys_spec tl tla _ _ _ h8)
      (eqCounts_spec tla tlb _ _ _ h9) hP1' e1 hgam1 etl hall hk htot hfit _ hV'
    rw [plG] at hr hb ht
    rw [thG] at ht
    refine ⟨by rw [fst_rowsForm]; exact nodup_of_rising hr, fun p hp => ?_,
      n1 ++ n2, n3, X, X4, hcl.symm.trans hl, hlen, by rw [l3, eNM, eReads], hFx ▸ hX, hX4, hG,
      by rw [ht, batch_rowsForm]⟩
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hp
    have := hb r hr'
    show F.planClaimsF ≤ r.1 ∧ r.1 ≤ F.planClaimsF + topOf tl funs - 1
    omega

#print axioms k08_claims

end VerifiableInference.Desc.First.TailClaims.Law
