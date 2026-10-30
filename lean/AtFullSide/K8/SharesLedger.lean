-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/SharesLedger.lean: the smallness test's stated number of the second fall (P1K8.k8ShareAt) is
small at each of the 25 segments: its denominator is positive and its numerator times 2 ^ 124 is at most the
denominator. The count that it states has six summands: each is bounded by crude bounds on the public
record's sizes, so no value of the public record is evaluated.

  addTreesF_J          behind addTreesF a matrix's shape holds at most one row of symbols in a row
  public_A_nU          an attention plan's third vector has the length nW
  blocks_le            piecesF's return has at most two blocks
  bz_le                the lookup's planes have at most 2 ^ 32 columns
  reads_le             a built segment's third vector of reads has at most 2 ^ 40 entries
  count_le             **the count, from these bounds**
  ledger_bound         **the stated number at each of the 25 segments**

Limits. Under the library's head, at the blank ground. A stated number bounds no chance here. The bounds are far from tight; that is all that they
are for. Nothing is claimed on completeness, soundness or hiding.
-/
import AtFullSide.K8.SharesBound
import Johnson.P1K8R.K9RowsByLink
import Johnson.P1K8R.UnitsAtPlans
import Johnson.P1K8R.SecondLaidAtBatch
import Johnson.Road.K4.Plan.U3ColsLay
import Johnson.Road.K4.Plan.ShapeRows
import Johnson.Desc.First.Att.Door.Law.K5U3Cols
import Johnson.Desc.ProofFile.Honest.K8.ColsFitAtBuilt
import OnBytes.Tie.Pv.Lookup.Ends.FoShapeZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.PlanWritten (tailView xShapeOf)
open Johnson.G (xShapeFull layoutFull)
open Meaning (viewTail)
open ProofFile.Honest (Odds)
open P5J (AtMgA TS)

/-! ## One row of symbols -/

/-- Every entry of the list holds at most one row of symbols in a row of the array. -/
def OneRow (T : Tail2) : Prop := ∀ x ∈ T.nt, (x.p.getD {}).J ≤ 1

theorem one_addN {F : Fork} {T : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) (g : OneRow T) : OneRow T' := by
  unfold t2AddN at h
  split at h
  · cases h
  · have e := Except.ok.inj h
    obtain ⟨_, e2⟩ := Prod.mk.inj e
    obtain ⟨_, e3⟩ := Prod.mk.inj e2
    subst e3
    intro x hx
    rcases Array.mem_push.1 hx with h1 | rfl
    · exact g x h1
    · exact Nat.zero_le _

theorem one_addP {F : Fork} {T : Tail2} {name : String} {m k w a : Nat} {foreign : Bool}
    {got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddP F T name m k w a foreign = .ok (got, F', T')) (g : OneRow T) : OneRow T' := by
  unfold t2AddP at h
  split at h
  · cases h
  · split at h
    · cases h
    · have e := Except.ok.inj h
      obtain ⟨_, e2⟩ := Prod.mk.inj e
      obtain ⟨_, e3⟩ := Prod.mk.inj e2
      subst e3
      intro x hx
      rcases Array.mem_push.1 hx with h1 | rfl
      · exact g x h1
      · exact Nat.le_refl _

theorem one_getD {T : Tail2} (g : OneRow T) (j : Nat) : ((T.nt.getD j {}).p.getD {}).J ≤ 1 := by
  rw [Array.getD_eq_getD_getElem?]
  cases hj : T.nt[j]? with
  | none => exact Nat.zero_le _
  | some x => exact g x (Array.mem_of_getElem? hj)

/-- **Behind addTreesF a matrix's shape has J at most 1.** -/
theorem addTreesF_J {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) :
    ∀ mu, mu < tl'.NM → (tl'.shp.getD mu {}).J ≤ 1 := by
  unfold addTreesF at h
  obtain ⟨h0, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F1, T1⟩, h1, h⟩ := ok_of_bind h
  obtain ⟨⟨F2, T2⟩, h2, h⟩ := ok_of_bind h
  obtain ⟨⟨F3, T3⟩, h3, h⟩ := ok_of_bind h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  have e := Except.ok.inj h
  obtain ⟨e1, -⟩ := Prod.mk.inj e
  have G0 : OneRow { T with link := true } := by
    intro x hx
    have hE : T.nt.isEmpty = true := by simpa using h0
    have hz : T.nt.size = 0 := Array.isEmpty_iff_size_eq_zero.1 hE
    obtain ⟨i, hi, _⟩ := Array.mem_iff_getElem.1 hx
    have hi' : i < T.nt.size := hi
    omega
  have K1 : OneRow T1 := forIn_keeps _ (List.range 3)
    (fun _ (s : MProd Fork Tail2) => OneRow s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      dsimp only at hs
      split at hs
      · obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
        obtain ⟨_, hs⟩ := ok_of_jp hs
        exact ⟨_, (Except.ok.inj hs).symm, one_addN hP hI⟩
      · exact ⟨_, (Except.ok.inj hs).symm, hI⟩)
    (List.range 3) [] _ _ rfl G0 h1
  have K2 : OneRow T2 := forIn_keeps _ (List.range tl.pkMat.size)
    (fun _ (s : MProd Fork Tail2) => OneRow s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, one_addP hP hI⟩)
    (List.range tl.pkMat.size) [] _ _ rfl K1 h2
  have K3 : OneRow T3 := forIn_keeps _ (List.range tl.pxMat.size)
    (fun _ (s : MProd Fork Tail2) => OneRow s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, one_addP hP hI⟩)
    (List.range tl.pxMat.size) [] _ _ rfl K2 h3
  have KB : OneRow TB := one_addN hB (one_addN hZ K3)
  have K4 : OneRow T4 := forIn_keeps _ (List.range tl.ft.size)
    (fun _ (s : MProd Fork Tail2) => OneRow s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, one_addP hP hI⟩)
    (List.range tl.ft.size) [] _ _ rfl KB h4
  intro mu hmu
  have hNM : tl'.NM = tl.NM := by rw [← e1]
  have hm : mu < tl.NM := by rw [← hNM]; exact hmu
  have hs : tl'.shp.getD mu {} = (T4.nt.getD (tl.gtTree.getD mu 0) {}).p.getD {} := by
    rw [← e1]
    show ((Array.range tl.NM).map fun mu =>
      (T4.nt.getD (tl.gtTree.getD mu 0) {}).p.getD {}).getD mu {} = _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_pos hm]
    rfl
  rw [hs]
  exact one_getD K4 _

/-- What a made record's shapes say. -/
theorem shp_of_made {tlc : HTailF2} (M : P1K8.Made tlc) {mu : Nat} (hm : mu < tlc.NM) :
    (tlc.shp.getD mu {}).J ≤ 1 ∧
      (tlc.shp.getD mu {}).mS = ((tlc.mats.getD mu {}).m + 2) / 3 := by
  obtain ⟨tl₀, tl, tl', m, txOf, f, hasU, tau, F, G, T, T', nU, aTX, hb, hbLine, hs, ha, hr⟩ := M
  have cS : tlc.shp = tl'.shp := congrArg (·.shp) hr
  have cM : tlc.mats = tl'.mats := congrArg (·.mats) hr
  have cN : tlc.NM = tl'.NM := congrArg (·.NM) hr
  rw [cS, cM]
  rw [cN] at hm
  exact ⟨addTreesF_J ha mu hm, OnBytes.Road.K4.Plan.addTreesF_mS ha mu hm⟩

/-! ## An attention plan's third vector -/

section
open _root_.Fo.BatRows _root_.Fo.Pub _root_.Fo.ZPlan
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_A_nU (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (a : Attention.Plan)
    (hg : X.A[g]? = some a) : a.seam.nU.getD 2 0 = a.nW := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    obtain ⟨seam0, -, h1, -⟩ := planA_rows0 _ _ _ a0 m2
    show a0.seam.nU.getD 2 0 = a0.nW
    rw [P1K8.seamPlan_nU h1]
    rfl
  · simp at e1

end

/-! ## The blocks and the planes -/

theorem blocks_le {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) : tl.zzBlocks ≤ 2 := by
  unfold HTailF2.piecesF at h
  obtain ⟨bz, _, h⟩ := ok_of_bind h
  obtain ⟨hb, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨f9, _, h⟩ := ok_of_bind h
  obtain ⟨pub, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  have e := (Except.ok.inj h).symm
  subst e
  show bz.size ≤ 2
  by_contra hc
  exact hb (by simp; omega)

theorem blocks_from_le {tl : HTailF2} (h : Fo.ZPlan.FromPieces tl) : tl.zzBlocks ≤ 2 := by
  obtain ⟨tl0, tlp, h1, h2⟩ := h
  unfold HTailF2.zzBlocks
  rw [h2.same.blocks]
  exact blocks_le h1

theorem bz_le {tl : HTailF2} (h : Fo.ZPlan.FromPieces tl) : tl.bzColumns ≤ 2 ^ 32 := by
  have hok := (Fo.ZPlan.shapeZ_from h).ok
  unfold FoNums.ok at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  have h1 : 2 ^ (tl.f9.d + 32) < OnBytes.pW.toNat := hok.2
  have h2 : OnBytes.pW.toNat < 2 ^ 64 := by decide
  have h3 : tl.f9.d + 32 < 64 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (h1.trans h2)
  show 2 ^ (tl.f9.kT + tl.f9.cK) ≤ 2 ^ 32
  have h4 : tl.f9.kT + tl.f9.cK ≤ 32 := by
    have : tl.f9.d = tl.f9.kT + tl.f9.cK := rfl
    omega
  exact Nat.pow_le_pow_right (by norm_num) h4

/-! ## Closed facts -/

/-- The written view: at most nine matrices and 2 ^ 28 rows of cells at each of the 25 segments. -/
theorem view_rows : (List.range 25).all (fun l =>
    decide ((viewTail xShapeFull l).1 ≤ 9) &&
      decide (((viewTail xShapeFull l).2.1.map (·.2.1)).sum ≤ 2 ^ 28)) = true := by decide +kernel

/-- The written layout: the reads' arrays have at most 2 ^ 40 columns. -/
theorem u3_le : (List.range 25).all (fun l =>
    (reqArray layoutFull l "U3").all fun A => decide (A.sizeC ≤ 2 ^ 40)) = true := by decide +kernel

/-- The head's third vector, as the written shape has it. -/
theorem head_nU : xShapeFull.2.1.getD 2 0 ≤ 2 ^ 40 := by decide +kernel

theorem ledger_num : 2 ^ 67 * (2 ^ 128 + 1) ^ 3 * 2 ^ 124 ≤ Code.pGold ^ 3 * 2 ^ 384 := by
  decide +kernel

/-! ## Small tools -/

theorem getD_le_sum : ∀ (L : List Nat) (i : Nat), L.getD i 0 ≤ L.sum
  | [], i => by simp
  | a :: t, 0 => by simp
  | a :: t, i + 1 => by
    have ih := getD_le_sum t i
    simp only [List.getD_cons_succ, List.sum_cons]
    omega

theorem list_sum_range (L : List Nat) (n : Nat) :
    ((List.range n).map fun i => L.getD i 0).sum = ∑ i ∈ Finset.range n, L.getD i 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

theorem tri_le (s : Nat) : ∀ n, ∑ k ∈ Finset.range n, s * k ≤ n * (s * n)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ]
    have ih := tri_le s n
    nlinarith

/-! ## The count -/

/-- **The count, from the bounds.** -/
theorem count_le {nU : Array Nat} {tl : HTailF2} {rows : Nat} (hn : nU.getD 2 0 ≤ 2 ^ 40)
    (hr : rows ≤ 2 ^ 26) (hmz : tl.mz ≤ 2 ^ 31) (hz : tl.zzBlocks ≤ 2) (hb : tl.bzColumns ≤ 2 ^ 32)
    (hm2 : ∑ mu ∈ Finset.range tl.NM, 2 * (tl.mats.getD mu {}).m ≤ 2 ^ 32)
    (hjk : ∑ mu ∈ Finset.range tl.NM, (tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k ≤ 24086)
    (hnm : tl.NM ≤ 9) (hs : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).mS ≤ 2 ^ 27)
    (ht : tl.stepF = 128) : P1K8.shareCount nU tl rows ≤ 2 ^ 67 := by
  unfold P1K8.shareCount
  have hR : rows - 1 ≤ 2 ^ 26 := Nat.le_trans (Nat.sub_le _ _) hr
  have t1 := Nat.mul_le_mul hn hR
  have t2 : 2 * (tl.zzBlocks * tl.mz) * (rows - 1) ≤ 2 * (2 * 2 ^ 31) * 2 ^ 26 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul hz hmz)) hR
  have t3 : (2 * tl.mz + ∑ mu ∈ Finset.range tl.NM, 2 * (tl.mats.getD mu {}).m) * (rows - 1) ≤
      (2 * 2 ^ 31 + 2 ^ 32) * 2 ^ 26 :=
    Nat.mul_le_mul (Nat.add_le_add (Nat.mul_le_mul_left _ hmz) hm2) hR
  have t4 : 3 * tl.bzColumns * (rows - 1) ≤ 3 * 2 ^ 32 * 2 ^ 26 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hb) hR
  have t5 := Nat.mul_le_mul hjk hR
  have t6 : ∑ mu ∈ Finset.range tl.NM, (1 + ∑ k ∈ Finset.range (tl.shp.getD mu {}).mS, tl.stepF * k) ≤
      9 * (1 + 2 ^ 27 * (128 * 2 ^ 27)) := by
    rw [ht]
    calc ∑ mu ∈ Finset.range tl.NM, (1 + ∑ k ∈ Finset.range (tl.shp.getD mu {}).mS, 128 * k)
        ≤ ∑ _mu ∈ Finset.range tl.NM, (1 + 2 ^ 27 * (128 * 2 ^ 27)) := by
          refine Finset.sum_le_sum fun mu hmu => ?_
          have hh := hs mu (Finset.mem_range.1 hmu)
          exact Nat.add_le_add_left
            ((tri_le 128 _).trans (Nat.mul_le_mul hh (Nat.mul_le_mul_left _ hh))) 1
      _ = tl.NM * (1 + 2 ^ 27 * (128 * 2 ^ 27)) := by simp
      _ ≤ 9 * (1 + 2 ^ 27 * (128 * 2 ^ 27)) := Nat.mul_le_mul_right _ hnm
  omega

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {G₀ : ProofFile.Ground}

theorem ms_le (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {l : Nat} (hl : l < 25) {Xl : LinkH}
    (hX : G₀.built[l]? = some Xl) : (Xl.tl.mats.toList.map (·.m)).sum ≤ 2 ^ 28 := by
  have hk : Xl.tl.mats.toList.map (·.m) = (viewTail xShapeFull l).2.1.map (·.2.1) := by
    rw [← view_at h hG hl hX]
    simp [tailView, Function.comp_def]
  rw [hk]
  have e := List.all_eq_true.1 view_rows l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at e
  exact of_decide_eq_true e.2

theorem nm_le (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {l : Nat} (hl : l < 25) {Xl : LinkH}
    (hX : G₀.built[l]? = some Xl) : Xl.tl.NM ≤ 9 := by
  have hk : Xl.tl.NM = (viewTail xShapeFull l).1 := congrArg (·.1) (view_at h hG hl hX)
  rw [hk]
  have e := List.all_eq_true.1 view_rows l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at e
  exact of_decide_eq_true e.1

/-- A built segment's third vector of reads, and that its record is what piecesF returned. -/
theorem reads_le (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {l : Nat} (hl : l < 25) {Xl : LinkH}
    (hX : G₀.built[l]? = some Xl) :
    (ProofFile.k8NU G₀ Xl).getD 2 0 ≤ 2 ^ 40 ∧ Fo.ZPlan.FromPieces Xl.tl := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  have hS := h.scope
  have hR := h.reads
  have eW : Bs.G₀.W = Zp.p.X := O.W
  have hXp : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.pubOne
  have h4 := (Meaning.scope_plans hS hR hXp).1
  have hy := (P5J.pins_of_laid hS h.laid).1
  have hLay : Zp.first.layout = layoutFull :=
    VerifiableInference.PlanWritten.Joined.layout_in_scope hS h.laid.pub hy
  have hu : ∀ k, k < 25 → ∀ A, reqArray Zp.first.layout k "U3" = some A → A.sizeC ≤ 2 ^ 40 := by
    intro k hk A hA
    have e := List.all_eq_true.1 u3_le k (List.mem_range.2 hk)
    rw [← hLay, hA] at e
    exact of_decide_eq_true e
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨-, X1, e1, hk, -⟩ := IM.ground_named hS hR O.pub O.blank
    obtain ⟨-, X2, e2, etl, -⟩ := IM.ground_tails hS hR O.pub O.blank
    obtain rfl : X1 = Xl := Option.some.inj (e1.symm.trans hX)
    obtain rfl : X2 = X1 := Option.some.inj (e2.symm.trans e1)
    have hnU : ProofFile.k8NU Bs.G₀ X2 = Bs.G₀.W.H.nU := by
      unfold ProofFile.k8NU
      simp [hk]
    refine ⟨?_, ?_⟩
    · rw [hnU, eW]
      have hV : xShapeOf Zp.p.X = xShapeFull :=
        VerifiableInference.PlanWritten.Joined.xShape_in_scope (o := OnBytes.secondHashFunction) hS h.laid.pub hy
      have e : Zp.p.X.H.nU.toList = xShapeFull.2.1 := by
        rw [← hV]
        rfl
      have e2' : Zp.p.X.H.nU.getD 2 0 = Zp.p.X.H.nU.toList.getD 2 0 := by
        rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]
      rw [e2', e]
      exact head_nU
    · rw [etl, eW]
      exact Fo.ZPlan.public_H_from hXp
  · obtain ⟨hN, -⟩ := IM.ground_named hS hR O.pub O.blank
    obtain ⟨hT, -⟩ := IM.ground_tails hS hR O.pub O.blank
    by_cases he : l % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
      have hg : g < 12 := by omega
      obtain ⟨X1, -, e1, hk, hXg, -⟩ := hN g hg
      obtain ⟨hp, a, X2, -, ehp, ea, e2, etl, -⟩ := hT g hg
      obtain rfl : X1 = Xl := Option.some.inj (e1.symm.trans hX)
      obtain rfl : X2 = X1 := Option.some.inj (e2.symm.trans e1)
      have hnU : ProofFile.k8NU Bs.G₀ X2 = hp.nU := by
        unfold ProofFile.k8NU
        simp [hk, hXg, ehp]
      rw [eW] at ehp ea
      refine ⟨?_, by rw [etl]; exact Fo.ZPlan.public_G_from hXp g hp ehp⟩
      obtain ⟨A, hA, -, hc⟩ := OnBytes.Road.K4.Plan.u3_array hXp h.laid.pub h4 ehp ea
      rw [hnU, ← hc]
      exact hu _ hl A hA
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
      have hg : g < 12 := by omega
      obtain ⟨-, X1, -, -, -, -, e1, hk, hXg, -⟩ := hN g hg
      obtain ⟨hp, a, -, X2, ehp, ea, -, -, -, -, -, -, e2, etl, -⟩ := hT g hg
      obtain rfl : X1 = Xl := Option.some.inj (e1.symm.trans hX)
      obtain rfl : X2 = X1 := Option.some.inj (e2.symm.trans e1)
      have hnU : ProofFile.k8NU Bs.G₀ X2 = a.seam.nU := by
        unfold ProofFile.k8NU
        simp [hk, hXg, ea]
      rw [eW] at ehp ea
      refine ⟨?_, by rw [etl]; exact Fo.ZPlan.public_A_from hXp g a ea⟩
      obtain ⟨A, hA, -, hc⟩ := H2K5.Door.u3_array_att hXp h.laid.pub h4 ehp ea
      rw [hnU, public_A_nU hXp g a ea, ← hc]
      exact hu _ hl A hA

/-- **The stated number of the second fall at each of the 25 segments.** -/
theorem ledger_bound (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {l : Nat} (hl : l < 25) :
    0 < (P1K8.k8ShareAt Zp G₀ l).den ∧
      (P1K8.k8ShareAt Zp G₀ l).num * 2 ^ 124 ≤ (P1K8.k8ShareAt Zp G₀ l).den := by
  obtain ⟨p, hp, hrows⟩ := P1K8.k9Rows_at_head OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg l hl
  cases hX : G₀.built[l]? with
  | none =>
    have e : P1K8.k8ShareAt Zp G₀ l = ⟨0, 1⟩ := by
      unfold P1K8.k8ShareAt
      rw [hX]
    rw [e]
    exact ⟨by norm_num, by norm_num⟩
  | some Xl =>
    have e : P1K8.k8ShareAt Zp G₀ l =
        P1K8.k8CountShare (ProofFile.k8NU G₀ Xl) Xl.tl p.rows := by
      unfold P1K8.k8ShareAt
      rw [hX, hp]
      rfl
    rw [e]
    obtain ⟨Bs, base, O⟩ := h.laid.opened
    obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
    have M := P1K8.made_at_built h.scope h.reads O hl hX
    obtain ⟨hn, hF⟩ := reads_le h hG hl hX
    have hrw : p.rows ≤ 2 ^ 26 := by
      rw [hrows]
      unfold P1K8.rowsAtLink
      split_ifs <;> norm_num
    have hsum := ms_le h hG hl hX
    have hmz : Xl.tl.mz ≤ 2 ^ 31 := by
      by_cases h0 : 0 < Xl.tl.NM
      · rw [P5J.K8N.mz_of_cols _ (ProofFile.Honest.K8.cols_at_built h.scope h.reads O hl hX) h0]
        have e3 : ∀ μ, (Xl.tl.mats.getD μ {}).m = (Xl.tl.mats.toList.map (·.m)).getD μ 0 :=
          fun μ => (P5J.K8N.getD_m _ μ).symm
        simp only [e3]
        rw [list_sum_range]
        exact Nat.le_trans (Nat.le_trans (sum_getD_le _ _) hsum) (by norm_num)
      · have hz := P1K8.made_sizes M
        unfold P1K8.sizesB at hz
        simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hz
        rcases hz.2 with a | a
        · exact absurd (Nat.pos_of_ne_zero a) h0
        · omega
    have hm2 : ∑ mu ∈ Finset.range Xl.tl.NM, 2 * (Xl.tl.mats.getD mu {}).m ≤ 2 ^ 32 := by
      rw [← Finset.mul_sum]
      have e3 : ∀ μ, (Xl.tl.mats.getD μ {}).m = (Xl.tl.mats.toList.map (·.m)).getD μ 0 :=
        fun μ => (P5J.K8N.getD_m _ μ).symm
      simp only [e3]
      have := Nat.le_trans (sum_getD_le (Xl.tl.mats.toList.map (·.m)) Xl.tl.NM) hsum
      omega
    have hjk : ∑ mu ∈ Finset.range Xl.tl.NM, (Xl.tl.shp.getD mu {}).J * (Xl.tl.shp.getD mu {}).k ≤
        24086 := by
      have hz := P1K8.made_sizes M
      unfold P1K8.sizesB at hz
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hz
      calc ∑ mu ∈ Finset.range Xl.tl.NM, (Xl.tl.shp.getD mu {}).J * (Xl.tl.shp.getD mu {}).k
          ≤ ∑ mu ∈ Finset.range Xl.tl.NM, (Xl.tl.mats.toList.map (·.k)).getD mu 0 := by
            refine Finset.sum_le_sum fun mu hmu => ?_
            have hm := Finset.mem_range.1 hmu
            rw [P5J.K8N.getD_k, ← (hz.1 mu hm).1.2]
            exact Nat.le_trans (Nat.mul_le_mul_right _ (shp_of_made M hm).1) (by omega)
        _ ≤ 24086 := Nat.le_trans (sum_getD_le _ _) (cols_le h hG hl hX)
    have hs : ∀ mu, mu < Xl.tl.NM → (Xl.tl.shp.getD mu {}).mS ≤ 2 ^ 27 := by
      intro mu hm
      rw [(shp_of_made M hm).2]
      have h1 := getD_le_sum (Xl.tl.mats.toList.map (·.m)) mu
      rw [P5J.K8N.getD_m] at h1
      omega
    have ht : Xl.tl.stepF = 128 := by
      unfold HTailF2.stepF
      rw [tau_at h hG hl hX]
      decide
    have hc := count_le hn hrw hmz (blocks_from_le hF) (bz_le hF) hm2 hjk (nm_le h hG hl hX) hs ht
    refine ⟨den_pos, ?_⟩
    show P1K8.shareCount (ProofFile.k8NU Bs.G₀ Xl) Xl.tl p.rows * (2 ^ 128 + 1) ^ 3 * 2 ^ 124 ≤
      Code.pGold ^ 3 * 2 ^ 384
    exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)) ledger_num

end AtFullSide.K8

#print axioms AtFullSide.K8.addTreesF_J
#print axioms AtFullSide.K8.public_A_nU
#print axioms AtFullSide.K8.reads_le
#print axioms AtFullSide.K8.count_le
#print axioms AtFullSide.K8.ledger_bound
