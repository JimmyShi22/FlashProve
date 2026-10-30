-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/LayersLaid.lean

Under the head (the terms: Johnson/HonestTrace/U3Fit/SeatsAtHead.lean), at each of the twelve groups
of layers, the laying of the layers' tables ("layTables") returns, and the laid length is the plan's
number of reads: two of the ten steps at which "layersVals" (Johnson/HonestTrace/U3Rows.lean) can
reject. Definitions and theorems. Public data alone.

How. The library has an inequality, "u3_cols_lay" (the tables end at or below the planned length),
and "u3_array" (the layout's array has the planned length as its columns):
Johnson/Road/K4/Plan/U3ColsLay.lean. The laid length hangs on seven lists of points' names that
"readsOf" makes. Each list is written by two truth values ("readsOf_lists"); eleven of the fourteen
are true by the library's laws on the segments; for the other three the inequality leaves one case
of eight, by a closed fact.

Main definitions: "longL", "shortL": the lists' forms. "asksBy", "triplesBy", "famBy": "tableAsks",
"K8.Asks.layers" and "famSum" as functions of what they read (each tied by rfl); "asksW",
"triplesW", "ksW", "msW", "sizesAt", "colsW": at the written values. "laidBy", the test: at each
group, of the eight cases the tables end at or below the columns in the case (no, no, no) alone, and
there the laying returns with the columns as its length, which is not 0.

Main theorems: "layersNums_at_head", "lists_at_head", "sizes_at_head", "tlOf_even"; and the end,
"layersLaid_at_head": for "G.W.G[g]? = some hp" the laying returns y with "y.2.2 = hp.nU.getD 2 0",
"y.2.2 = colsW (2 * g)" and "y.2.2 ≠ 0". It stands at the rows and columns "sizesOf hp.tl.mats"; the
maker lays at "matsOf Q": that the two are one is the maker's step in front, which
Johnson/HonestTrace/U3Fit/LayersAtHead.lean shows.

Limits. The head is a premise: the full size and the format's second hash function alone. Two closed facts,
"laidW_yes" and "laidW_can_fail" (two controls), are shown by "decide +kernel", each under
"set_option maxRecDepth 1000000", which raises the elaborator's depth of recursion. In both controls
it is the comparison of the laid length that fails; nothing in this file turns the comparison over
the eight cases by itself. No theorem of its own says that "asksW", "triplesW", "colsW" are the
values of "tableAsks", of "K8.Asks.layers" and of the array's columns under the head: the end's
proof shows it on its way.
Not claimed: more than these two steps; anything on the tables' entries. No property of a release,
of a verifier or of a prover is claimed.
-/
import Johnson.HonestTrace.U3Fit.Slice
import Johnson.HonestTrace.U3Fit.MatsAtHead
import Johnson.Road.K4.Plan.U3ColsLay
import Johnson.Goal.Meaning.Pub34All
import Johnson.Road.FormsKeysCaller

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Lay Reads readsOf TableAsk tableAsks layTables)
open OnBytes.Road (anyZ anyR refuse_bind)
open ProofFile (Pub Ground)
open ProofFile.Honest.K3 (tlOf linkH stepOf)
open Johnson.G (layoutFull)
open P5J (AtMgA TS)

/-! ## 1 The seven lists -/

/-- A long table's points. -/
def longL (z v r ab p3 : Bool) : List String :=
  (if z then ["Z"] else []) ++ (if v then ["Z_V"] else []) ++ (if r then ["Y"] else []) ++
    (if ab then ["Z_a"] ++ (if p3 then ["Z_b"] else []) else [])

/-- A short table's points. -/
def shortL (z pv r : Bool) : List String :=
  (if z then ["zt"] else []) ++ (if pv then ["P_V", "r_tV"] else []) ++ (if r then ["rt"] else [])

/-- **GENERAL: the seven lists that "readsOf" returns.** -/
theorem readsOf_lists {y : Lay} {rd : Reads} (h : readsOf y = .ok rd) :
    rd.rdAF = longL (anyZ y 'f') true (anyR y 'f') true y.h.p3 ∧
      rd.rdQA = longL (anyZ y 'q') false (anyR y 'q') false y.h.p3 ∧
      rd.rdXI = longL (anyZ y 'i') true (anyR y 'i') false y.h.p3 ∧
      rd.rdXO = longL (anyZ y 'o') false (anyR y 'o') false y.h.p3 ∧
      rd.rdAD = shortL (anyZ y 'd') false (anyR y 'd') ∧
      rd.rdAR = shortL (anyZ y 'r') true (anyR y 'r') ∧
      rd.rdQS = shortL (anyZ y 'Q') false (anyR y 'Q') := by
  unfold readsOf at h
  have h2 := refuse_bind h
  have e := (Except.ok.inj h2).symm
  subst e
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem long_Z {z v r ab p : Bool} (h : "Z" ∈ longL z v r ab p) : z = true := by
  cases z
  · cases v <;> cases r <;> cases ab <;> cases p <;> exact absurd h (by decide)
  · rfl

theorem long_Y {z v r ab p : Bool} (h : "Y" ∈ longL z v r ab p) : r = true := by
  cases r
  · cases z <;> cases v <;> cases ab <;> cases p <;> exact absurd h (by decide)
  · rfl

theorem short_zt {z pv r : Bool} (h : "zt" ∈ shortL z pv r) : z = true := by
  cases z
  · cases pv <;> cases r <;> exact absurd h (by decide)
  · rfl

theorem short_rt {z pv r : Bool} (h : "rt" ∈ shortL z pv r) : r = true := by
  cases r
  · cases z <;> cases pv <;> exact absurd h (by decide)
  · rfl

/-! ## 2 What the two lists of families read -/

/-- "tableAsks" of what it reads. -/
def asksBy (nAF nAD La T mb : Nat) (p4 : Bool) (AF QA XI XO AD AR QS : List String) (g : Nat) :
    List TableAsk :=
  let iAR := nAF + nAD
  let tables (mn : String) (M0 parts : Nat) (pts : List String) (lng : Bool) : List TableAsk :=
    pts.map fun n => ⟨mn ++ "@" ++ n, M0, parts, if lng then La else T, n, lng⟩
  tables "af" 0 nAF AF true ++
  tables "qa" (iAR + 2) 1 QA true ++
  tables "xbI" (iAR + 4) 1 XI true ++
  (if g == 0 then tables "xbI" (iAR + 4) 1 ["Z_E"] true else []) ++
  tables "xbO" (iAR + 3) 1 XO true ++
  tables "ad" nAF nAD AD false ++
  tables "ar" iAR 1 AR false ++
  (if p4 then tables "qa" (iAR + 2) 1 QS false else []) ++
  [⟨"b-bits-0", iAR + 1, 1, mb, "", false⟩, ⟨"b-bits-1", iAR + 1, 1, mb, "", false⟩,
   ⟨"b-pin", iAR + 1, 1, mb, "", false⟩]

theorem tableAsks_by (y : Lay) (rd : Reads) (g : Nat) :
    tableAsks y rd g = asksBy (y.parts.getD 0 0) (y.parts.getD 1 0) (2 ^ y.h.la) y.T (2 ^ y.h.lmb)
      y.h.p4 rd.rdAF rd.rdQA rd.rdXI rd.rdXO rd.rdAD rd.rdAR rd.rdQS g := rfl

/-- "K8.Asks.layers" of what it reads. -/
def triplesBy (nAF nAD La T mb : Nat) (p4 : Bool) (AF QA XI XO AD AR QS : List String) (g : Nat) :
    List (Nat × Nat × Nat) :=
  let iAR := nAF + nAD
  List.replicate AF.length (0, nAF, La) ++
  List.replicate QA.length (iAR + 2, 1, La) ++
  List.replicate XI.length (iAR + 4, 1, La) ++
  (if g == 0 then [(iAR + 4, 1, La)] else []) ++
  List.replicate XO.length (iAR + 3, 1, La) ++
  List.replicate AD.length (nAF, nAD, T) ++
  List.replicate AR.length (iAR, 1, T) ++
  (if p4 then List.replicate QS.length (iAR + 2, 1, T) else []) ++
  List.replicate 3 (iAR + 1, 1, mb)

theorem layers_by (y : Lay) (rd : Reads) (g : Nat) :
    VerifiableInference.Desc.First.K8.Asks.layers y rd g =
      triplesBy (y.parts.getD 0 0) (y.parts.getD 1 0) (2 ^ y.h.la) y.T (2 ^ y.h.lmb) y.h.p4 rd.rdAF
        rd.rdQA rd.rdXI rd.rdXO rd.rdAD rd.rdAR rd.rdQS g := rfl

/-- The library's "famSum" of the two lists that it reads. -/
def famBy (ks ms : List Nat) (a : Nat × Nat × Nat) : Nat :=
  ((List.range a.2.1).map fun q => ks.getD (a.1 + q) 0 * (ms.getD (a.1 + q) 0 / a.2.2)).sum

theorem famSum_by (p : VerifiableInference.Desc.First.K8.Par) :
    OnBytes.Road.K4.Plan.famSum p = famBy p.ks p.ms := rfl

/-! ## 3 At the written values -/

def asksW (rq ro rQ : Bool) (g : Nat) : List TableAsk :=
  asksBy 3 1 65536 1024 65536 true (longL true true true true true)
    (longL true false rq false true) (longL true true true false true)
    (longL true false ro false true) (shortL true false true) (shortL true true true)
    (shortL true false rQ) g

def triplesW (rq ro rQ : Bool) (g : Nat) : List (Nat × Nat × Nat) :=
  triplesBy 3 1 65536 1024 65536 true (longL true true true true true)
    (longL true false rq false true) (longL true true true false true)
    (longL true false ro false true) (shortL true false true) (shortL true true true)
    (shortL true false rQ) g

/-- The columns, the rows, and both, of the matrices of a segment's written list. -/
def ksW (k : Nat) : List Nat := (viewsW.getD k []).map (·.2.2.2)
def msW (k : Nat) : List Nat := (viewsW.getD k []).map (·.2.2.1)
def sizesAt (k : Nat) : Array (Nat × Nat) :=
  ((viewsW.getD k []).map fun v => (v.2.2.1, v.2.2.2)).toArray

/-- The columns of the written layout's array "U3" at a segment. -/
def colsW (k : Nat) : Nat := ((reqArray layoutFull k "U3").map (·.sizeC)).getD 0

/-- **A TEST AT WRITTEN VALUES.** cols: the array's columns at a segment. At each group: of the eight cases
of the three open truth values, the tables end at or below the columns in the case (no, no, no) alone; and
in that case the laying returns, and its length is the columns, which are not 0. -/
def laidBy (cols : Nat → Nat) : Bool :=
  (List.range 12).all fun g =>
    ([false, true].all fun rq => [false, true].all fun ro => [false, true].all fun rQ =>
      !decide (((triplesW rq ro rQ g).map (famBy (ksW (2 * g)) (msW (2 * g)))).sum ≤ cols (2 * g)) ||
        (!rq && !ro && !rQ)) &&
    match layTables (sizesAt (2 * g)) (asksW false false false g) 0 with
    | some x => x.2.2 == cols (2 * g) && cols (2 * g) != 0
    | none => false

set_option maxRecDepth 1000000 in
theorem laidW_yes : laidBy colsW = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Controls: with 400 columns more · with one column less: the test says no: by its clause on the length. -/
theorem laidW_can_fail :
    (laidBy (fun k => colsW k + 400) || laidBy fun k => colsW k - 1) = false := by decide +kernel

/-! ## 4 Under the head -/

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- The views of X's own list at a segment are the written ones. -/
theorem view_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {k : Nat} (hk : k < 25) :
    (tlOf G.W k).mats.toList.map matView = viewsW.getD k [] := by
  rw [← views_at_head h hG]
  exact (views_getD G.W hk).symm

/-- The rows and columns of X's own list at a segment are the written ones. -/
theorem sizes_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {k : Nat} (hk : k < 25) :
    sizesOf (tlOf G.W k).mats = sizesAt k := by
  unfold sizesAt sizesOf
  rw [← view_at_head h hG hk, List.map_map]
  apply Array.ext'
  rw [Array.toList_map]
  rfl

theorem ks_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {k : Nat} (hk : k < 25) :
    (tlOf G.W k).mats.toList.map (·.k) = ksW k := by
  unfold ksW
  rw [← view_at_head h hG hk, List.map_map]
  rfl

theorem ms_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {k : Nat} (hk : k < 25) :
    (tlOf G.W k).mats.toList.map (·.m) = msW k := by
  unfold msW
  rw [← view_at_head h hG hk, List.map_map]
  rfl

/-- Under the marks the structure at an even segment is the group's plan's. -/
theorem tlOf_even {X : Verify.Public} (M : PlanMarks X) {g : Nat} (hg : g < 12)
    {hp : Layer.HPlan2} (e : X.G[g]? = some hp) : tlOf X (2 * g) = hp.tl := by
  have e1 : stepOf X = 2 := by
    unfold stepOf
    rw [M.p4]
    rfl
  have e2 : linkH X = 24 := by
    unfold linkH
    rw [e1, M.groups]
  have a : (2 * g == 24) = false := by
    have : 2 * g ≠ 24 := by omega
    simpa using this
  have b : (2 * g % 2 == 0) = true := by
    have : 2 * g % 2 = 0 := by omega
    rw [this]
    rfl
  have c : 2 * g / 2 = g := by omega
  unfold tlOf
  rw [e1, e2, a, b, c, e]
  rfl

/-- **The numbers that the two lists of families read.** -/
theorem layersNums_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    G.W.y.parts.getD 0 0 = 3 ∧ G.W.y.parts.getD 1 0 = 1 ∧ 2 ^ G.W.y.h.la = 65536 ∧
      G.W.y.T = 1024 ∧ 2 ^ G.W.y.h.lmb = 65536 ∧ G.W.y.h.p4 = true ∧ G.W.y.h.p3 = true := by
  have hX := IM.ground_publicK h.laid.pub hG
  have N := partsFit_in_scope h.scope h.reads hX
  have A := OnBytes.Road.Hd.core_of_scope h.scope h.reads hX
  have eh := OnBytes.Road.shape_of_public hX
  obtain ⟨hy, S, -, -, -, -, -, -, -, -, -, h4⟩ := Meaning.P34.pub34_public h.scope h.reads hX
  have hla : G.W.y.h.la = 16 := by
    rw [eh]
    exact A.num 12
  have hlt : G.W.y.h.lt = 10 := by
    rw [eh]
    exact A.num 1
  have hN : G.W.y.NGr = 12 := (marks_at_head h hG).groups
  obtain ⟨hp, -, -, -, e0, -⟩ := (IM.ground_tails h.scope h.reads h.laid.pub hG).1 0 (by decide)
  have t0 : sizesOf hp.tl.mats = sizesAt 0 := by
    rw [← tlOf_even (marks_at_head h hG) (by decide : 0 < 12) e0]
    exact sizes_at_head h hG (by decide)
  have t1 : sizesOf hp.tl.mats = (OnBytes.Road.sizesTab G.W.y).toArray :=
    ((Meaning.P34.tails_of_public hX e0).1).trans
      (OnBytes.Road.tails_pairs G.W.y (by rw [hN]; decide))
  have t2 := congrArg (fun a : Array (Nat × Nat) => (a.getD 5 (0, 0)).1) (t1.symm.trans t0)
  have hmb : 2 ^ G.W.y.h.lmb = 65536 := by
    unfold OnBytes.Road.sizesTab at t2
    rw [N.af, N.ad] at t2
    exact t2
  refine ⟨N.af, N.ad, by rw [hla]; norm_num, ?_, hmb, by rw [eh]; exact h4, by rw [eh]; exact S.p3⟩
  rw [(OnBytes.Road.laid2_of_layout hy).T, hlt]
  norm_num

/-- **The seven lists: eleven truth values are had; three stay letters.** -/
theorem lists_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    ∃ rq ro rQ : Bool,
      G.W.layers.rd.rdAF = longL true true true true true ∧
      G.W.layers.rd.rdQA = longL true false rq false true ∧
      G.W.layers.rd.rdXI = longL true true true false true ∧
      G.W.layers.rd.rdXO = longL true false ro false true ∧
      G.W.layers.rd.rdAD = shortL true false true ∧
      G.W.layers.rd.rdAR = shortL true true true ∧
      G.W.layers.rd.rdQS = shortL true false rQ := by
  have hX := IM.ground_publicK h.laid.pub hG
  obtain ⟨hy, S, -, hrd, -⟩ := Meaning.P34.pub34_public h.scope h.reads hX
  obtain ⟨-, -, -, -, -, q4, q3⟩ := layersNums_at_head h hG
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := readsOf_lists hrd
  let v : Layer.Env := { y := G.W.y, sc := G.W.layers.sc, g := 0, iU3 := 0, K3 := 0, tab := [], zk := #[] }
  have hy' : Layer.layout (Verify.layerShape G.W.P) G.W.P.polCalls = .ok v.y := hy
  have hrd' : readsOf v.y = .ok G.W.layers.rd := hrd
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := OnBytes.Road.points_of_layout hy' S hrd'
  obtain ⟨n1, n2, n3, n4⟩ := OnBytes.Road.points2_of_layout hy' S hrd'
  have zQ : anyZ G.W.y 'Q' = true :=
    OnBytes.Road.anyZ_of_seg (OnBytes.Road.hasSeg_of_layout hy' S .O) (by
      rw [q4]
      decide)
  rw [a1] at m1 n1
  rw [a2] at m2
  rw [a3] at m3 n2
  rw [a4] at m4
  rw [a5] at m5 n3
  rw [a6] at m6 n4
  rw [long_Z m1, long_Y n1, q3] at a1
  rw [long_Z m2, q3] at a2
  rw [long_Z m3, long_Y n2, q3] at a3
  rw [long_Z m4, q3] at a4
  rw [short_zt m5, short_rt n3] at a5
  rw [short_zt m6, short_rt n4] at a6
  rw [zQ] at a7
  exact ⟨_, _, _, a1, a2, a3, a4, a5, a6, a7⟩

/-- **UNDER THE HEAD, AT EACH GROUP: THE LAYING RETURNS, AND ITS LENGTH IS THE PLAN's NUMBER OF READS**, which is
the written layout's array's columns, and not 0. -/
theorem layersLaid_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : Nat} (hg : g < 12)
    {hp : Layer.HPlan2} (e : G.W.G[g]? = some hp) :
    ∃ y, layTables (sizesOf hp.tl.mats) (tableAsks G.W.layers.y G.W.layers.rd g) 0 = some y ∧
      y.2.2 = hp.nU.getD 2 0 ∧ y.2.2 = colsW (2 * g) ∧ y.2.2 ≠ 0 := by
  have hX := IM.ground_publicK h.laid.pub hG
  have M := marks_at_head h hG
  obtain ⟨p0, p1, pla, pT, pmb, p4, -⟩ := layersNums_at_head h hG
  obtain ⟨rq, ro, rQ, l1, l2, l3, l4, l5, l6, l7⟩ := lists_at_head h hG
  obtain ⟨ls, -, eW, -, eF⟩ := IM.blank_ground hG
  -- the segment's built data
  obtain ⟨hp', a, Xl, -, e', ea, e3, t1, -⟩ :=
    (IM.ground_tails h.scope h.reads h.laid.pub hG).1 g hg
  obtain rfl : hp = hp' := Option.some.inj (e.symm.trans e')
  obtain ⟨Xl', -, f2, kd, kg, -⟩ := (IM.ground_named h.scope h.reads h.laid.pub hG).1 g hg
  obtain rfl : Xl = Xl' := Option.some.inj (e3.symm.trans f2)
  have etl := tlOf_even M hg e
  have hk : 2 * g < 25 := by omega
  -- the two lists of families
  have eA : tableAsks G.W.layers.y G.W.layers.rd g = asksW rq ro rQ g := by
    rw [tableAsks_by]
    show asksBy (G.W.y.parts.getD 0 0) (G.W.y.parts.getD 1 0) (2 ^ G.W.y.h.la) G.W.y.T
      (2 ^ G.W.y.h.lmb) G.W.y.h.p4 _ _ _ _ _ _ _ g = _
    rw [p0, p1, pla, pT, pmb, p4, l1, l2, l3, l4, l5, l6, l7]
    rfl
  have eT : (ProofFile.k8Par Zp G Xl (2 * g)).asks = triplesW rq ro rQ g := by
    show ProofFile.k8Asks G Xl = _
    unfold ProofFile.k8Asks
    rw [kd, kg]
    show VerifiableInference.Desc.First.K8.Asks.layers G.W.y G.W.layers.rd g = _
    rw [layers_by, p0, p1, pla, pT, pmb, p4, l1, l2, l3, l4, l5, l6, l7]
    rfl
  have eks : (ProofFile.k8Par Zp G Xl (2 * g)).ks = ksW (2 * g) := by
    show Xl.tl.mats.toList.map (·.k) = _
    rw [t1, ← etl]
    exact ks_at_head h hG hk
  have ems : (ProofFile.k8Par Zp G Xl (2 * g)).ms = msW (2 * g) := by
    show Xl.tl.mats.toList.map (·.m) = _
    rw [t1, ← etl]
    exact ms_at_head h hG hk
  -- the layout's array
  have eL : Zp.first.layout = layoutFull := by
    rw [← eF]
    exact (first_at_head h hG).2.2
  obtain ⟨A, a1, -, a3⟩ :=
    OnBytes.Road.K4.Plan.u3_cols_lay h.scope h.reads h.laid.pub hG hg e3
  rw [OnBytes.Road.K4.Plan.end_sum0, eT, famSum_by, eks, ems] at a3
  have eC : A.sizeC = colsW (2 * g) := by
    unfold colsW
    rw [← eL, a1]
    rfl
  rw [eW] at e ea
  obtain ⟨A', b1, -, b3⟩ := OnBytes.Road.K4.Plan.u3_array (by rw [← eW]; exact hX) h.laid.pub
    (by rw [← eW]; exact M.p4) e ea
  obtain rfl : A = A' := Option.some.inj (a1.symm.trans b1)
  -- the closed fact
  have w := List.all_eq_true.1 laidW_yes g (List.mem_range.2 hg)
  rw [Bool.and_eq_true] at w
  obtain ⟨w1, w2⟩ := w
  have mem : ∀ b : Bool, b ∈ [false, true] := fun b => by cases b <;> decide
  have w3 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 w1 rq (mem rq)) ro (mem ro))
    rQ (mem rQ)
  rw [eC] at a3
  rw [decide_eq_true a3] at w3
  have w4 : (!rq && !ro && !rQ) = true := w3
  obtain ⟨rfl, rfl, rfl⟩ : rq = false ∧ ro = false ∧ rQ = false := by
    cases rq <;> cases ro <;> cases rQ <;> first | exact ⟨rfl, rfl, rfl⟩ | cases w4
  have eS : sizesOf hp.tl.mats = sizesAt (2 * g) := by
    rw [← etl]
    exact sizes_at_head h hG hk
  rw [eS, eA]
  cases hl : layTables (sizesAt (2 * g)) (asksW false false false g) 0 with
  | none =>
    rw [hl] at w2
    cases w2
  | some y =>
    rw [hl] at w2
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at w2
    exact ⟨y, rfl, by rw [w2.1, ← eC, b3], w2.1, by rw [w2.1]; exact w2.2⟩

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement, and the axioms that it rests on: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.readsOf_lists
#check @OnBytes.HonestTrace.U3.Fit.long_Z
#check @OnBytes.HonestTrace.U3.Fit.long_Y
#check @OnBytes.HonestTrace.U3.Fit.short_zt
#check @OnBytes.HonestTrace.U3.Fit.short_rt
#check @OnBytes.HonestTrace.U3.Fit.tableAsks_by
#check @OnBytes.HonestTrace.U3.Fit.layers_by
#check @OnBytes.HonestTrace.U3.Fit.famSum_by
#check @OnBytes.HonestTrace.U3.Fit.laidW_yes
#check @OnBytes.HonestTrace.U3.Fit.laidW_can_fail
#check @OnBytes.HonestTrace.U3.Fit.view_at_head
#check @OnBytes.HonestTrace.U3.Fit.sizes_at_head
#check @OnBytes.HonestTrace.U3.Fit.ks_at_head
#check @OnBytes.HonestTrace.U3.Fit.ms_at_head
#check @OnBytes.HonestTrace.U3.Fit.tlOf_even
#check @OnBytes.HonestTrace.U3.Fit.layersNums_at_head
#check @OnBytes.HonestTrace.U3.Fit.lists_at_head
#check @OnBytes.HonestTrace.U3.Fit.layersLaid_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.readsOf_lists
#print axioms OnBytes.HonestTrace.U3.Fit.long_Z
#print axioms OnBytes.HonestTrace.U3.Fit.long_Y
#print axioms OnBytes.HonestTrace.U3.Fit.short_zt
#print axioms OnBytes.HonestTrace.U3.Fit.short_rt
#print axioms OnBytes.HonestTrace.U3.Fit.tableAsks_by
#print axioms OnBytes.HonestTrace.U3.Fit.layers_by
#print axioms OnBytes.HonestTrace.U3.Fit.famSum_by
#print axioms OnBytes.HonestTrace.U3.Fit.laidW_yes
#print axioms OnBytes.HonestTrace.U3.Fit.laidW_can_fail
#print axioms OnBytes.HonestTrace.U3.Fit.view_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.sizes_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.ks_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.ms_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.tlOf_even
#print axioms OnBytes.HonestTrace.U3.Fit.layersNums_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.lists_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.layersLaid_at_head
