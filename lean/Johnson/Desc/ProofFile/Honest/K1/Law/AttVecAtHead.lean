-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/AttVecAtHead.lean: AT AN ATTENTION's READS, AT THE HEAD: THE HONEST MAKER OF THE
VECTOR OF READS RETURNS AT WHAT WAS HEARD, AND ITS VECTOR IS THE READING AT THE STATE's OWN TABLES. The form VecTie
(AtFullSide/K1/ReadsCore.lean), at every letter wit: valsAt at an odd segment does not read the cover (valsAt_att_at_head).

  merged_planes_same, placeOk_same   what tablesP tests of the points are the same at two lists that meet PtsTo
  fits_parts, mem_lay, partStep, lay_foldl, askYes, partsFit_of_tables   the four tests of partsFit off tablesP's return
  planFit_att    the test on lengths, on the plan's numbers, at the lookup's lengths
  attVals_vec_returns   where ptsOf, tablesP and partsFit return the maker's vector returns
  vec_att_head   THE CLAIM

NO PROPERTY IS CLAIMED.
IDLE WHERE ThrS HOLDS OF NOTHING.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.AttFunsAtHead
import Johnson.Desc.K5.Honest.Law.PublicAtHead
import Johnson.Goal.Meaning.PlanOwn
import Johnson.HonestTrace.U3Fit.ValsSorts
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsPointsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att (funBack tabsBack)
open VerifiableInference.Desc.First.Att.P (Pts Geo LookIn TablesP ScoreP RemP Fun1 lastCoords mergedPlanes mergedTokens)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Model (HTailF2 TMat)
open OnBytes.HonestTrace (pairOf heardOf parOfMats parFits_parOfMats SameSizes ParFits.same readAt_same)
open OnBytes.HonestTrace.U3 (u3Seats placeIn sizesOf SegVals valsAt attVals covOf partsFit ask have_)
open H2K5.Honest (PtsTo KeySame TableFields table_fields pointsSame_of_fields unitView Pub5 Chal)
open H2K5.Honest.PointsFields (tilesV)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K3 (lookHeardAt OpenSame matsOwn)
open ProofFile.Honest.K4 (k4LookOf)
open ProofFile.Honest.K8 (cellsAtOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 tablesP's tests -/

/-- The test on the planes reads their points alone. -/
theorem merged_planes_same {n : ℕ} {zx : Array OnBytes.E} {q p : Pts}
    (h : q.planes.toList.map H2K5.Honest.remKey = p.planes.toList.map H2K5.Honest.remKey) :
    mergedPlanes n zx q.planes = mergedPlanes n zx p.planes := by
  have e : ∀ a : Array RemP, a.all (fun pc => lastCoords pc.z n == lastCoords zx n) =
      (a.toList.map H2K5.Honest.remKey).all (fun k => lastCoords k.2.1 n == lastCoords zx n) := by
    intro a
    rw [List.all_map, ← Array.all_toList]
    rfl
  unfold mergedPlanes
  rw [e, e, h]

/-- **Where the honest points meet the verifier's, tablesP's one test says at them what it says at the verifier's.** -/
theorem placeOk_same {x : OnBytes.Params.AttentionRounds} {g : Geo} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : LookIn}
    {q p : Pts} (K : ∀ n, PtsTo x n q p) (h : K5Law.placeOk g mats nW lk p = true) :
    K5Law.placeOk g mats nW lk q = true := by
  have key := (K 0).key
  have TF : TableFields q p := table_fields K
  have PS : K5Law.laidBy g lk q = K5Law.laidBy g lk p := pointsSame_of_fields g lk TF
  have hd := key.d
  simp only [H2K5.Honest.divKey, Prod.mk.injEq] at hd
  have hsz : q.scores.size = p.scores.size := by
    have e := congrArg List.length key.scores
    simpa using e
  have e1 := merged_planes_same (n := g.lmS) (zx := lk.zx) key.planes
  have e2 : mergedTokens g lk.zx q.d = mergedTokens g lk.zx p.d := by
    unfold mergedTokens
    rw [TF.ziW, TF.zcW, hd.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2]
  have e3 : (First.Att.P.reads q.scores.size).all (fun r => (K5Law.tabs g lk q r).all (K5Law.fitsT mats)) =
      (First.Att.P.reads p.scores.size).all (fun r => (K5Law.tabs g lk p r).all (K5Law.fitsT mats)) := by
    rw [← List.all_flatMap, ← List.all_flatMap, ← K5Law.laidBy_eq, ← K5Law.laidBy_eq, PS]
  have hri : q.x.ri g = p.x.ri g := by
    unfold First.Att.P.MaxP.ri
    rw [TF.scF]
  have hrc : q.x.rc g = p.x.rc g := by
    unfold First.Att.P.MaxP.rc
    rw [TF.scF]
  have hpj : q.x.pj g = p.x.pj g := by
    unfold First.Att.P.MaxP.pj
    rw [TF.scd]
  have e4 : (First.Att.P.reads q.scores.size).all (K5Law.longOk g lk q) =
      (First.Att.P.reads p.scores.size).all (K5Law.longOk g lk p) := by
    have eu : ∀ l : List ScoreP, l.all (fun k =>
        K5Law.lngB g (lastCoords k.sc.r g.ldh) (First.Att.P.tok g (First.Att.P.scoreTiles g k).1 k.zi) &&
          (K5Law.lngB g (lastCoords k.sc.r g.ldh) (First.Att.P.tok g (First.Att.P.scoreTiles g k).2 k.zj) && true)) =
        (l.map unitView).all (fun v =>
          K5Law.lngB g (lastCoords v.2.2.2.2 g.ldh) (First.Att.P.tok g (tilesV g v.2.2.2.1 v.2.2.2.2).1 v.2.1) &&
            (K5Law.lngB g (lastCoords v.2.2.2.2 g.ldh) (First.Att.P.tok g (tilesV g v.2.2.2.1 v.2.2.2.2).2 v.2.2.1) &&
              true)) := fun l => by
      rw [List.all_map]
      rfl
    rw [K5Law.longs_eq, K5Law.longs_eq, eu, eu, TF.scores, TF.zcW, TF.ziW, TF.scE, TF.wJv, TF.vpm, TF.vpd, hrc, hri,
      hpj]
  unfold K5Law.placeOk at h ⊢
  rw [e1, e2, e3, e4, hsz]
  exact h

/-! ## 2 partsFit off tablesP's return -/

/-- What fits says. -/
theorem fits_parts {Sz : Array (ℕ × ℕ)} {mat len e : ℕ} (h : First.Att.P.fits Sz mat len e = true) :
    ∃ M, Sz[mat]? = some M ∧ len ≠ 0 ∧ M.1 % len = 0 ∧ e = M.2 * (M.1 / len) := by
  unfold First.Att.P.fits at h
  cases hM : Sz[mat]? with
  | none =>
    rw [hM] at h
    cases h
  | some M =>
    rw [hM] at h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
    exact ⟨M, rfl, h.1.1, h.1.2, h.2⟩

/-- What is laid comes from a table. -/
theorem mem_lay : ∀ (Ls : List K5Law.Table) (m : ℕ) (f : Fun1), f ∈ K5Law.layFrom m Ls →
    ∃ T ∈ Ls, f.mat = T.mat ∧ f.len = T.len
  | [], _, _, h => by cases h
  | T :: Ls, m, f, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨T, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨T', hT, b⟩ := mem_lay Ls _ f h'
      exact ⟨T', List.mem_cons_of_mem _ hT, b⟩

/-- A list of parts as partsFit reads it. -/
def partOf (f : Fun1) : ℕ × ℕ × ℕ × ℕ := (f.mat, f.len, f.phi.size, f.start)

/-- partsFit's last test's step. -/
def partStep (Sz : Array (ℕ × ℕ)) (s : Option ℕ) (f : ℕ × ℕ × ℕ × ℕ) : Option ℕ :=
  s.bind fun p =>
    if f.2.2.2 == p then some (p + (Sz.getD f.1 (0, 0)).2 * ((Sz.getD f.1 (0, 0)).1 / f.2.1)) else none

/-- Tables that fit follow one another. -/
theorem lay_foldl (Sz : Array (ℕ × ℕ)) : ∀ (Ls : List K5Law.Table) (m : ℕ), Ls.all (K5Law.fitsT Sz) = true →
    ((K5Law.layFrom m Ls).map partOf).foldl (partStep Sz) (some m) = some (m + K5Law.total Ls)
  | [], m, _ => rfl
  | T :: Ls, m, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨M, hM, -, -, he⟩ := fits_parts h.1
    have eg : Sz.getD T.mat (0, 0) = M := by
      rw [Array.getD_eq_getD_getElem?, hM]
      rfl
    have st : partStep Sz (some m) (partOf ⟨T.mat, T.len, T.phi, 2, m⟩) = some (m + T.entries) := by
      show (if m == m then some (m + (Sz.getD T.mat (0, 0)).2 * ((Sz.getD T.mat (0, 0)).1 / T.len)) else none) = _
      rw [eg, he]
      simp
    show ((K5Law.layFrom (m + T.entries) Ls).map partOf).foldl (partStep Sz)
      (partStep Sz (some m) (partOf ⟨T.mat, T.len, T.phi, 2, m⟩)) = _
    rw [st, lay_foldl Sz Ls (m + T.entries) h.2, K5Law.total_cons, Nat.add_assoc]

theorem askYes {n : String} {b : Bool} (h : b = true) : ask n b = .ok () := by
  unfold ask
  rw [if_pos h]

/-- **partsFit says yes at the tables that tablesP returns, where each has as many weights as its length.** -/
theorem partsFit_of_tables {g : Geo} {nW : ℕ} {lk : LookIn} {p : Pts} {t : TablesP} {mats : Array TMat}
    (ht : First.Att.P.tablesP g (sizesOf mats) nW lk p = some t)
    (hphi : ∀ f ∈ t.funs.toList, f.phi.size = f.len) :
    partsFit (sizesOf mats) (t.funs.toList.map fun f => (f.mat, f.len, f.phi.size, f.start)) nW = .ok () := by
  have hl := K5Law.tablesP_laid ht
  have hf := K5Law.tablesP_fits ht
  have htot := K5Law.total_is_nW ht
  have each : ∀ f ∈ t.funs.toList, ∃ M, (sizesOf mats)[f.mat]? = some M ∧ f.len ≠ 0 ∧ M.1 % f.len = 0 := by
    intro f hm
    rw [hl] at hm
    obtain ⟨T, hT, e1, e2⟩ := mem_lay _ _ f hm
    obtain ⟨M, hM, h0, h1, -⟩ := fits_parts (List.all_eq_true.1 hf T hT)
    exact ⟨M, by rw [e1]; exact hM, by rw [e2]; exact h0, by rw [e2]; exact h1⟩
  have b1 : ((t.funs.toList.map fun f => (f.mat, f.len, f.phi.size, f.start)).all
      fun f => decide (f.1 < (sizesOf mats).size)) = true := by
    refine List.all_eq_true.2 fun f hm => ?_
    obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hm
    obtain ⟨M, hM, -, -⟩ := each f' hf'
    exact decide_eq_true (Array.getElem?_eq_some_iff.1 hM).1
  have b2 : ((t.funs.toList.map fun f => (f.mat, f.len, f.phi.size, f.start)).all
      fun f => f.2.1 != 0 && ((sizesOf mats).getD f.1 (0, 0)).1 % f.2.1 == 0) = true := by
    refine List.all_eq_true.2 fun f hm => ?_
    obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hm
    obtain ⟨M, hM, h0, h1⟩ := each f' hf'
    have eg : (sizesOf mats).getD f'.mat (0, 0) = M := by
      rw [Array.getD_eq_getD_getElem?, hM]
      rfl
    show (f'.len != 0 && ((sizesOf mats).getD f'.mat (0, 0)).1 % f'.len == 0) = true
    rw [eg]
    simp [h0, h1]
  have b3 : ((t.funs.toList.map fun f => (f.mat, f.len, f.phi.size, f.start)).all
      fun f => f.2.2.1 == f.2.1) = true := by
    refine List.all_eq_true.2 fun f hm => ?_
    obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hm
    show (f'.phi.size == f'.len) = true
    rw [hphi f' hf']
    simp
  have b4 : (((t.funs.toList.map fun f => (f.mat, f.len, f.phi.size, f.start)).foldl
      (fun (s : Option ℕ) f => s.bind fun p =>
        if f.2.2.2 == p then
          some (p + ((sizesOf mats).getD f.1 (0, 0)).2 * (((sizesOf mats).getD f.1 (0, 0)).1 / f.2.1))
        else none) (some 0)) == some nW) = true := by
    rw [hl]
    have q := lay_foldl (sizesOf mats) _ 0 hf
    rw [Nat.zero_add, htot] at q
    have q' : ((K5Law.layFrom 0 (K5Law.laidBy g lk p)).map fun f => (f.mat, f.len, f.phi.size, f.start)).foldl
        (partStep (sizesOf mats)) (some 0) = some nW := q
    exact beq_iff_eq.2 q'
  unfold partsFit
  rw [askYes b1, askYes b2, askYes b3, askYes b4]
  rfl

/-! ## 3 The maker -/

private theorem okBind {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem someHave {α : Type} {n : String} {o : Option α} {a : α}
    (h : have_ n o = .ok a) : o = some a := by
  cases o with
  | none => cases h
  | some x => exact congrArg some (Except.ok.inj h)

/-- **Where ptsOf, tablesP and partsFit return, the maker's vector returns.** -/
theorem attVals_vec_returns {Z : ProofFile.Pub} {G : ProofFile.Ground} {sps : List Spot} {seg g : ℕ} {V : SegVals}
    (hV : attVals Z G sps seg g = .ok V) {A : OnBytes.Attention.Plan} {k5 k3 : Spot × ℕ}
    (hA : G.W.A[g]? = some A) (h5 : placeIn Z sps seg .K5 = .ok k5) (h3 : placeIn Z sps seg .K3 = .ok k3)
    {heard : List Fmt.Drawn} {p : Pts} {t : TablesP}
    (hp : H2K5.Honest.ptsOf ⟨A.S, A.own⟩ ⟨(k4LookOf A.fs k3.2 heard).zk, heard.drop k5.2⟩ = some p)
    (ht : First.Att.P.tablesP (⟨A.S, A.own⟩ : Pub5).g (sizesOf A.mats) A.nW
      (First.Att.P.lookOf A.S.cf.lmb (k4LookOf A.fs k3.2 heard)) p = some t)
    (hf : partsFit (sizesOf A.mats) (t.funs.toList.map fun f => (f.mat, f.len, f.phi.size, f.start)) A.nW = .ok ()) :
    V.vec heard = .ok fun C => H2K5.Honest.u3Of (sizesOf A.mats)
      (fun a r c => OnBytes.Model.ofInt (cellsAtOf C (matsOwn G.W seg) a r c)) t.funs := by
  unfold attVals at hV
  obtain ⟨A₁, hA₁, hV⟩ := okBind hV
  obtain rfl : A = A₁ := Option.some.inj (hA.symm.trans (someHave hA₁))
  obtain ⟨k5₁, e5, hV⟩ := okBind hV
  obtain rfl : k5 = k5₁ := Except.ok.inj (h5.symm.trans e5)
  obtain ⟨k3₁, e3, hV⟩ := okBind hV
  obtain rfl : k3 = k3₁ := Except.ok.inj (h3.symm.trans e3)
  dsimp only at hV
  obtain ⟨_, _, hV⟩ := okBind hV
  obtain ⟨_, _, hV⟩ := okBind hV
  obtain ⟨_, _, hV⟩ := okBind hV
  have eV := Except.ok.inj hV
  subst eV
  dsimp only
  have e : ((H2K5.Honest.ptsOf ⟨A.S, A.own⟩ ⟨(k4LookOf A.fs k3.2 heard).zk, heard.drop k5.2⟩).bind fun p =>
      First.Att.P.tablesP (⟨A.S, A.own⟩ : Pub5).g (sizesOf A.mats) A.nW
        (First.Att.P.lookOf A.S.cf.lmb (k4LookOf A.fs k3.2 heard)) p) = some t := by
    rw [hp]
    exact ht
  rw [e]
  show (partsFit _ _ _ >>= _) = _
  rw [hf]
  rfl

/-! ## 4 The test on lengths -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The test on lengths says yes on the plan's numbers, at a lookup's lengths.** -/
theorem planFit_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) {K : First.Shape.HeardAll}
    (hK : K.shape = a.fs) (hx : K.zx = a.fs.dT) (h0 : K.zb0 = 5 + a.fs.d) (h1 : K.zb1 = 5 + a.fs.d)
    (hpl : First.Look.planesOk a.fs a.S.cf.lmb = true) :
    H2K5.Honest.planFitB (First.Att.P.parCOf a).geo a.own K = true := by
  obtain ⟨hid, PL⟩ := H2K5.Honest.law_at_head h hg ea
  have N := OnBytes.Road.Rows.norm_of_hid hid
  have Zs := OnBytes.Road.Rows.sizes_of_hid hid
  have OS := Meaning.own_of_shape h.scope h.reads h.pubOne hg ea
  have fD : a.S.nD ≤ a.fs.dT := by
    have e : (OnBytes.Road.L5.dimOf a.S).lD = a.S.nD := N.nD.symm
    have := PL.fit.2.2.2.2.2.2.1.2.1
    rw [e] at this
    exact this
  have hlm := Zs.lmS
  have hlnT := Zs.lnT
  have hnD := N.nD
  have hlt := N.lt
  unfold First.Look.planesOk at hpl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpl
  unfold H2K5.Honest.planFitB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · show a.S.cf.lmS ≤ K.zx
    omega
  · show a.S.cf.lmS ≤ H2K5.Honest.lenM (First.Att.P.geoOf a.S) a.own.valueM
    rw [OS.valueM]
    show a.S.cf.lmS ≤ min (a.S.cf.lgk + 2 * a.S.lnT - 1) (a.S.cf.lgk + 2 * a.S.lnT - 1 + a.S.cf.lB) +
      (min (a.S.lnT + a.S.cf.lB) a.S.cf.lt - a.S.lnT) + min a.S.cf.lB (a.S.cf.lgk + 2 * a.S.lnT - 1 + a.S.cf.lB)
    omega
  · show a.S.cf.lmS ≤ H2K5.Honest.lenD (First.Att.P.geoOf a.S) a.own.valueD
    rw [OS.valueD]
    show a.S.cf.lmS ≤ min (a.S.cf.lgk + a.S.lnT) (a.S.cf.lgk + a.S.lnT + a.S.cf.lB) +
      (min (a.S.lnT + a.S.cf.lB) a.S.cf.lt - a.S.lnT) + min a.S.cf.lB (a.S.cf.lgk + a.S.lnT + a.S.cf.lB)
    omega
  · exact Zs.T.symm
  · show a.S.cf.lgk + a.S.cf.lt ≤ 2 * a.own.lgk + 2 * a.own.lt + 4
    rw [OS.lgk, OS.lt]
    omega
  · show 2 * a.S.cf.lt + a.S.cf.lgk ≤ a.own.lt + a.own.lgk + a.own.lt
    rw [OS.lgk, OS.lt]
    omega
  · show a.S.cf.lt ≤ a.own.bits
    rw [OS.bits]
    show a.S.cf.lt ≤ a.S.cf.lt + a.S.cf.lgk + 4
    omega
  · show H2K5.Honest.lenB K.shape a.S.cf.lmb K.zb0 = a.S.cf.lmb
    rw [hK, h0]
    unfold H2K5.Honest.lenB OnBytes.Model.Forest.Shape.d
    omega
  · show H2K5.Honest.lenB K.shape a.S.cf.lmb K.zb1 = a.S.cf.lmb
    rw [hK, h1]
    unfold H2K5.Honest.lenB OnBytes.Model.Forest.Shape.d
    omega

end

/-- The lookup's two points zb have 5 + d coordinates, whatever was heard. -/
theorem zb_sizes (fs : OnBytes.Model.Forest.Shape) (base : ℕ) (L : List Fmt.Drawn) :
    (lookHeardAt fs base L).zb0.size = 5 + fs.d ∧ (lookHeardAt fs base L).zb1.size = 5 + fs.d := by
  constructor
  · show (List.toArray (List.map _ (List.range (5 + fs.d)))).size = _
    simp
  · show (List.toArray (List.map _ (List.range (5 + fs.d)))).size = _
    simp

/-! ## 5 The claim -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)

/-- **AT AN ATTENTION's READS THE HONEST MAKER RETURNS AT WHAT WAS HEARD, AND ITS VECTOR IS THE READING AT THE STATE's OWN
TABLES.** hTl: the state in front has the plan's record (attTlS_head). wit is free: valsAt at an odd segment does not read
the cover. -/
theorem vec_att_head {g : ℕ} (hg : g < 12) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {A : OnBytes.Attention.Plan}
    (hA : G.W.A[g]? = some A) {Ad : MsgAddr} {am : ℕ}
    (hPair : pairOf (u3Seats Zp G) Ad = some (2 * g + 1, am))
    (hTl : AttTlS (𝕋) Said (K1.noL (2 * g + 1) false) A)
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst) :
    ∀ blk, (𝕋).bs[K1.noL (2 * g + 1) false]? = some blk → ∀ k s μ E ds y cols s',
      ThrS (𝕋).thread Said (K1.noL (2 * g + 1) false) k s μ E →
      drawsFit blk.rounds ds = true → (𝕋).thread.Stepped blk k s μ E ds y cols s' →
      ∀ tl : HTailF2, s'.tl? = some tl →
      ∃ (SV : SegVals) (vec : Cells → ℕ → OnBytes.E),
        valsAt Zp G ((covOf Zp G (wit μ.st.input).x).toOption.getD default) (2 * g + 1) = .ok SV ∧
        SV.vec (μ.st.heard.take (heardOf (u3Seats Zp G) Ad)) = .ok vec ∧
        SV.n = A.nW ∧
        ∀ (C : Cells) (j : ℕ), j < A.nW → vec C j =
          First.K8.Honest.readAt (parOfMats tl.mats) tl.funs.toList
            (cellsAtOf C (matsOwn G.W (2 * g + 1))) j := by
  intro blk hb k s μ E ds y cols s' hT hd hS tl htl
  obtain ⟨k5, k3, Hh, hd5, Lf, pv, t₀, a, nx, q5, q3, Op, hpv, hSame, ht₀, htl', hsh⟩ :=
    attRun h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hg hG hPair hb hT hS hA
  obtain rfl := Option.some.inj (htl.symm.trans htl')
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have hW : Bs.G₀.W = P5J.At.X Zp := O.W
  have hAX : (P5J.At.X Zp).A[g]? = some A := hW ▸ hA
  -- the public maker
  obtain ⟨V, hV, hVn, -⟩ := OnBytes.HonestTrace.U3.Att.attVals_at_head h hG hg
  have hVv : ∀ cov, valsAt Zp Bs.G₀ cov (2 * g + 1) = .ok V := fun cov => by
    rw [OnBytes.HonestTrace.U3.Fit.valsAt_att_at_head h hG hg]
    exact hV
  obtain ⟨A₂, k5₂, k3₂, eA₂, e5₂, e3₂, en₂, -⟩ := K5.attVals_vec hV
  obtain rfl : A = A₂ := Option.some.inj (hA.symm.trans eA₂)
  obtain rfl : k5 = k5₂ := Except.ok.inj (q5.symm.trans e5₂)
  obtain rfl : k3 = k3₂ := Except.ok.inj (q3.symm.trans e3₂)
  -- the honest points return
  have pa := K5Law.points_are hpv
  have nL : Lf.scores.size = (H2K5.Honest.blankLeft A.own.score.length).scores.size := by
    have e1 := pa.nL.symm.trans (pa.nH.trans (hSame 0).nS)
    simpa [H2K5.Honest.heardAt, H2K5.Honest.blankLeft] using e1
  obtain ⟨p₀, hp₀, -⟩ := H2K5.Honest.points_congr (hSame 0).nR (hSame 0).nS nL hpv
  have hp₀' : H2K5.Honest.ptsOf ⟨A.S, A.own⟩
      ⟨Hh.zk, (μ.st.heard.take (heardOf (u3Seats Zp Bs.G₀) Ad)).drop k5.2⟩ = some p₀ := hp₀
  have K : ∀ n, PtsTo A.own n p₀ pv := fun n =>
    H2K5.Honest.points_same ⟨A.S, A.own⟩ (hSame n) hp₀' hpv
  -- the honest tables return
  have hok : K5Law.placeOk (First.Att.P.parCOf A).geo (First.Att.P.parCOf A).mats (First.Att.P.parCOf A).nW
      (First.Att.P.lookOfO (First.Att.P.parCOf A).geo.lmb Hh) pv = true := by
    rw [← K5Law.tablesP_isSome, ht₀]
    rfl
  obtain ⟨t, ht⟩ := K5Law.tablesP_some (placeOk_same K hok)
  have hfun : t.funs = t₀.funs := H2K5.Honest.funs_same
    (H2K5.Honest.points_laid K _ _) ht ht₀
  -- as many weights as rows
  have hpl : (First.Att.P.lookOfO (First.Att.P.parCOf A).geo.lmb Hh).planesOk = true := by
    unfold K5Law.placeOk at hok
    simp only [Bool.and_eq_true] at hok
    exact hok.1.1.1.2
  have hsz := ProofFile.Honest.K3.Law.AtThr.lookHeardAt_sizes A.fs k3.2
    (μ.st.heard.take (heardOf (u3Seats Zp Bs.G₀) Ad))
  have hG' : H2K5.Honest.tabsFitB (First.Att.P.parCOf A).geo (First.Shape.heard5Sh hd5)
      (First.Shape.heardAll Hh) = true := by
    rw [hsh, H2K5.Honest.tabsFitB_at]
    have hlook : First.Look.planesOk Hh.shape A.S.cf.lmb = true := hpl
    rw [Op.shape] at hlook
    refine planFit_att h hg hAX ?_ ?_ ?_ ?_ hlook
    · exact Op.shape
    · show Hh.zx.size = _
      rw [Op.zx]
      exact hsz.1
    · show Hh.zb0.size = _
      rw [Op.zb0]
      exact (zb_sizes _ _ _).1
    · show Hh.zb1.size = _
      rw [Op.zb1]
      exact (zb_sizes _ _ _).2
  have hfit : First.Att.P.fit (First.Att.P.parCOf A).geo
      (First.Att.P.lookOfO (First.Att.P.parCOf A).geo.lmb Hh) pv = true := by
    rw [K5Law.fit_eq_ten hok]
    exact H2K5.Honest.fitTen_of hpv hG' hpl
  have hphi : ∀ f ∈ t.funs.toList, f.phi.size = f.len := fun f hf => by
    rw [hfun] at hf
    exact (H2K5.Honest.funs_fit ht₀ hfit f hf).2
  have hzk : (k4LookOf A.fs k3.2 (μ.st.heard.take (heardOf (u3Seats Zp Bs.G₀) Ad))).zk = Hh.zk := Op.zk.symm
  have hvec := attVals_vec_returns hV hA q5 q3
    (heard := μ.st.heard.take (heardOf (u3Seats Zp Bs.G₀) Ad)) (p := p₀) (t := t)
    (by rw [hzk]; exact hp₀')
    (by rw [lookOf_of_open Op]; exact ht)
    (partsFit_of_tables (mats := A.mats) ht hphi)
  refine ⟨V, _, hVv _, hvec, en₂, fun C j _ => ?_⟩
  -- the reading
  have hl2 : 2 * g + 1 < 25 := by omega
  obtain ⟨e, Xl, reads, he, hX, hu⟩ := K1.k01_flat_reads h.scope h.reads O (2 * g + 1) hl2
  obtain ⟨m0, m1, -, -, -, -, f2, k2, g2, -⟩ := (IM.ground_named h.scope h.reads O.pub O.blank).1 g hg
  obtain rfl : m1 = Xl := Option.some.inj (f2.symm.trans hX)
  have hU := IM.alone_underR hu
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  have hAg : Bs.G₀.W.A[m1.g]? = some A := by
    rw [g2]
    exact hA
  obtain ⟨r₁, r₂, gs, -, -, -, -, -, -, -, hdec, -, -, -, -, -, -, -, -, -⟩ :=
    att_record (L := 𝕋) k2 hAg hU hS
  obtain ⟨a₀, hs0, hL0⟩ := hTl _ hb k s μ E ds y cols s' hT hd hS
  obtain ⟨tl', htl'', hL1⟩ :=
    K1.tlLike_over_reads Zp Bs.G₀ (2 * g + 1) m1 hX _ reads s s' [r₁, r₂] gs rfl hdec a₀ hs0
  obtain rfl := Option.some.inj (htl''.symm.trans htl)
  have hL := hL0.trans hL1
  show H2K5.Honest.u3Of (sizesOf A.mats) (fun a r c => OnBytes.Model.ofInt (cellsAtOf C (matsOwn Bs.G₀.W (2 * g + 1)) a r c))
    t.funs j = _
  rw [K1.u3Of_is_readAt A.mats (cellsAtOf C (matsOwn Bs.G₀.W (2 * g + 1))) t.funs j, hfun]
  refine readAt_same (mats := _) (ParFits.same ?_ (parFits_parOfMats A.mats)) (parFits_parOfMats _) _ _ _
  rw [hL.mats]
  exact SameSizes.refl _

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.placeOk_same
#print axioms ProofFile.Honest.K1.partsFit_of_tables
#print axioms ProofFile.Honest.K1.attVals_vec_returns
#print axioms ProofFile.Honest.K1.planFit_att
#print axioms ProofFile.Honest.K1.vec_att_head
