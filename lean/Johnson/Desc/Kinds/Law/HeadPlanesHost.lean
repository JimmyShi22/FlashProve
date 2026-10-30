-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadPlanesHost.lean: what the output head owes its lookup on the planes of
the lookup's counts, under the law of the reads, from a yes of the description's own text that makes
the head's tables.

Law/HeadPlanes.lean states the head's instance of the planes' law (Johnson/Meaning/PlanesKit.lean)
with the tables as premises: three tables found in a table of tables, long enough, laid in a list
under the lookup's own weights. Here these premises are shown of the text that lays the tables:
K8.ReadsQuiet.tables (Johnson/Desc/K8/ReadsQuiet.lean), and of the record that the block
K8.ReadsQuiet.head leaves. The form follows the layers' instance, Johnson/Meaning/PlanesHost.lean.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  tables_asks: a yes of tables: the tables are what the library's list of fifteen asks makes
      (Fo.asksH, Fo.askStep), at the lookup's own weights Forest.phiB at 0 and 1.
  laid_of_tabIs: a table of one part, found under its name (Fo.TabIs): its row in the table of
      tables, its length, and that it is laid in the list (Meaning.Planes.LaidAt).
  tables_planes: so the three tables of the planes, after a yes of tables.
  k6_host_planes: THE THREE CLAUSES (Meaning.Planes.K3HostPlanes) AT THE HEAD'S READERS, in any
      world with the law of the reads at the tables that the text made.
  k6_host_underReads: the same for all cells and all entries that meet the law of the reads.
  TabsLie h L hp s o cov x t: the record s stands in the head's link, opened, and holds what the
      head heard (x) and the tables (t) that the text makes of x and of the covered positions; the
      record of the smallness test in s has the plan's matrices, their number and the plan's
      numbers of the arrays, and the list of these tables.
  tabsLie_behind: TabsLie holds behind a yes of the block K8.ReadsQuiet.head.
  readsQuiet_keeps: that block leaves what S.look?, S.lookHeard? and S.fork? read.
  k6_host_planes_at: the three clauses at the seat's own reader (planesAt) at a record with TabsLie,
      with the law of the reads asked at the record's own matrices and list.

Every letter under "there is", and the clause that pins it. tables_asks: ZV, lowN, qFC, qROW by the
description's own makers (Johnson/Desc/Own/HeadTabs.lean); b0, b1 by Forest.phiB. laid_of_tabIs: e
by find?. tables_planes: b0, b1 by Forest.phiB; e0, e1, eP by find?. tabsLie_behind: o, cov, x, t by
TabsLie's fields here, covered, heard, laid. k6_host_planes_at: r by callerReaders.

Premises that nobody pays here. THE LAW OF THE READS (Fo.ReadsAll). The planes' matrix, number
NHf + 2 of the plan's list, has its rows in one block of 2 ^ lmbH and at least the planes' columns
(hm, hk: hm is on public numbers; hk reads the shape in the lookup's record). Its cells are the
lookup's (h4; hcm). cols, the width at which the law of the reads is asked, is a letter in
k6_host_planes; in k6_host_planes_at it is the width of the array iU3 in the record's ledger, which
is asked to be there, with a column (htr, hK0): the seat's reader refuses else. iU3 is a letter
throughout.
Limits. Ties in one world: no draw, no error term, nothing on soundness. No values are shown at
which the premises hold together. That a later record still has TabsLie is not shown: tabsLie_behind
speaks of the record right behind the block. That x.g1 is what the lookup's run "planes" reads
(S.lookHeard?) is not shown here.
-/
import Johnson.Desc.Kinds.Law.HeadPlanes
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.Own.HeadTabsAgree
import OnBytes.Tie.Pv.Lookup.Ends.FoReadsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law
open Cb Cb.Fo Cb.Fo.NumsEq TwV
open OnBytes OnBytes.Model Fo Meaning.Planes
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8

/-! ## What a yes of the text that makes the tables says -/

/-- **A yes of the head's tables: they are what the list of fifteen asks makes**, at the lookup's
own weights. -/
theorem tables_asks {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {x : Model.Head.Heard} {t : Model.Head.Tables}
    (e : ReadsQuiet.tables h L hp cov x = .ok t) :
    ∃ ZV lowN qFC qROW b0 b1, Own.tailOf x.wpl.r h.la = some ZV ∧
      Own.cutTail (Model.Head.zjOf L x.g1 x.qN) h.ls = some lowN ∧
      Own.callWith L "CNF" = some qFC ∧ Own.callWith L "ROW" = some qROW ∧
      Forest.phiB x.g1 h.lmbH 0 = some b0 ∧ Forest.phiB x.g1 h.lmbH 1 = some b1 ∧
      (asksH h L cov x ZV (longPoint lowN.2 x.tN.r) qFC qROW b0 b1).foldlM
        (askStep hp.tl.mats) {} = some t := by
  unfold ReadsQuiet.tables at e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨ZV, p1, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨lowN, p2, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨qFC, p3, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨qROW, p4, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨b0, z0, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨b1, z1, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨t', e3, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  simp only [pure, Except.pure, Except.ok.injEq] at e
  subst e
  exact ⟨ZV, lowN, qFC, qROW, b0, b1, ReadsQuiet.named_ok p1, ReadsQuiet.named_ok p2,
    ReadsQuiet.named_ok p3, ReadsQuiet.named_ok p4,
    (Own.planeWeights_agrees _ _ _).trans (ReadsQuiet.named_ok z0),
    (Own.planeWeights_agrees _ _ _).trans (ReadsQuiet.named_ok z1), ReadsQuiet.named_ok e3⟩

/-- A table of one part, found under its name: its row in the table of tables, its length, and that
it is laid in the list. -/
theorem laid_of_tabIs {mats : Array TMat} {t : Model.Head.Tables} {nm : String} {M0 lm : Nat}
    {phi : Array E} (T : TabIs mats t nm M0 1 (2 ^ lm) phi) :
    ∃ e : String × Nat × Nat, (t.tab.find? fun e => e.1 == nm) = some e ∧
      e.2.2 = (mats.getD M0 {}).k * ((mats.getD M0 {}).m / 2 ^ lm) ∧
      LaidAt t.funs e.2.1 M0 (2 ^ lm) phi := by
  obtain ⟨p0, len, e1, e2, e3⟩ := T
  refine ⟨(nm, p0, len), e1, ?_, partRec mats M0 (2 ^ lm) p0 phi 0, e3 0 Nat.one_pos, rfl, rfl,
    rfl, rfl, rfl⟩
  show len = _
  rw [e2]
  show p0 + partLen mats (2 ^ lm) (M0 + 0) - p0 = _
  rw [Nat.add_sub_cancel_left]
  rfl

/-- **The three tables of the planes, after a yes of the head's tables.** -/
theorem tables_planes {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {x : Model.Head.Heard} {t : Model.Head.Tables}
    (e : ReadsQuiet.tables h L hp cov x = .ok t) :
    ∃ (b0 b1 : Array E) (e0 e1 eP : String × Nat × Nat),
      Forest.phiB x.g1 h.lmbH 0 = some b0 ∧ Forest.phiB x.g1 h.lmbH 1 = some b1 ∧
      (t.tab.find? fun e => e.1 == "bH-bits-0") = some e0 ∧
      (t.tab.find? fun e => e.1 == "bH-bits-1") = some e1 ∧
      (t.tab.find? fun e => e.1 == "bH-pin") = some eP ∧
      e0.2.2 = (hp.tl.mats.getD (h.NHf + 1 + 1) {}).k *
        ((hp.tl.mats.getD (h.NHf + 1 + 1) {}).m / 2 ^ h.lmbH) ∧
      e1.2.2 = (hp.tl.mats.getD (h.NHf + 1 + 1) {}).k *
        ((hp.tl.mats.getD (h.NHf + 1 + 1) {}).m / 2 ^ h.lmbH) ∧
      eP.2.2 = (hp.tl.mats.getD (h.NHf + 1 + 1) {}).k *
        ((hp.tl.mats.getD (h.NHf + 1 + 1) {}).m / 2 ^ h.lmbH) ∧
      LaidAt t.funs e0.2.1 (h.NHf + 1 + 1) (2 ^ h.lmbH) b0 ∧
      LaidAt t.funs e1.2.1 (h.NHf + 1 + 1) (2 ^ h.lmbH) b1 ∧
      LaidAt t.funs eP.2.1 (h.NHf + 1 + 1) (2 ^ h.lmbH) (Forest.phiP h.lmbH) := by
  obtain ⟨ZV, lowN, qFC, qROW, b0, b1, _, _, _, _, y0, y1, ea⟩ := tables_asks e
  obtain ⟨e0, h0, l0, T0⟩ := laid_of_tabIs (tab_bits0 ea)
  obtain ⟨e1, h1, l1, T1⟩ := laid_of_tabIs (tab_bits1 ea)
  obtain ⟨eP, hP, lP, TP⟩ := laid_of_tabIs (tab_pin ea)
  exact ⟨b0, b1, e0, e1, eP, y0, y1, h0, h1, hP, l0, l1, lP, T0, T1, TP⟩

/-- A table of the planes' matrix is long enough, where the matrix has its rows in one block and at
least the planes' columns. -/
theorem len_fits {n k m lm len : Nat} (hm : m / 2 ^ lm = 1) (hk : n ≤ k)
    (hl : len = k * (m / 2 ^ lm)) : n ≤ len := by
  rw [hl, hm, Nat.mul_one]
  exact hk

/-! ## The debt, paid under the law of the reads -/

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- **The three clauses of the host's law on the planes, at the head's readers**, in any world that
meets the law of the reads at the tables that the text made. iU3, cols: the array of the reads and
the width at which the law of the reads is asked. -/
theorem k6_host_planes {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {x : Model.Head.Heard} {t : Model.Head.Tables}
    (e : ReadsQuiet.tables h L hp cov x = .ok t) {cellM : Nat → Nat → Nat → K} {iU3 cols : Nat}
    (hm : (hp.tl.mats.getD (h.NHf + 1 + 1) {}).m / 2 ^ h.lmbH = 1)
    (hk : planeCols x.g1.shape h.lmbH ≤ (hp.tl.mats.getD (h.NHf + 1 + 1) {}).k)
    (ν : _root_.Fo.Pl → K)
    (h4 : ∀ r < 2 ^ h.lmbH, ∀ c < planeCols x.g1.shape h.lmbH,
      cellM (h.NHf + 1 + 1) r c = ν (.cell r c))
    (W : World K) (hA : ReadsAll ρ hp.tl.mats t.funs W.entry iU3 cols cellM) :
    K3HostPlanes x.g1.shape h.lmbH (rdL ρ x.g1.zb0) (rdL ρ x.g1.zb1) ν (fun f => f.value ρ W)
      (fun e col => (planeEntry t.tab iU3 cols (if e == 0 then .bits0 else .bits1) col).getD {})
      (fun col => (planeEntry t.tab iU3 cols .pin col).getD {}) := by
  obtain ⟨b0, b1, e0, e1, eP, y0, y1, h0, h1, hP, l0, l1, lP, T0, T1, TP⟩ := tables_planes e
  exact head_host_planes ρ x.g1 y0 y1 h0 h1 hP (len_fits hm hk l0) (len_fits hm hk l1)
    (len_fits hm hk lP) T0 T1 TP hm hk ν h4 W hA

/-- **The three clauses at the head's readers, for all cells and all entries that meet the law of
the reads.** cm: where the matrices' cells lie; hcm: the cells of the planes' matrix lie where the
lookup's do. -/
theorem k6_host_underReads {J₀ : Type} {h : Model.Head.Shape} {L : Model.Head.HL}
    {hp : Model.Head.HPlanH2} {cov : Model.Head.Covered} {x : Model.Head.Heard}
    {t : Model.Head.Tables} (e : ReadsQuiet.tables h L hp cov x = .ok t) (iU3 cols : Nat)
    (hm : (hp.tl.mats.getD (h.NHf + 1 + 1) {}).m / 2 ^ h.lmbH = 1)
    (hk : planeCols x.g1.shape h.lmbH ≤ (hp.tl.mats.getD (h.NHf + 1 + 1) {}).k)
    (H : Fork) (mk : Nat → J₀) (pl : Nat → Nat → J₀) (cm : Nat → Nat → Nat → J₀)
    (hcm : ∀ r < 2 ^ h.lmbH, ∀ c < planeCols x.g1.shape h.lmbH, cm (h.NHf + 1 + 1) r c = pl r c) :
    K3HostPlanesUnderReads ρ H x.g1.shape h.lmbH (rdL ρ x.g1.zb0) (rdL ρ x.g1.zb1) mk pl
      hp.tl.mats t.funs iU3 cols cm
      (fun e col => (planeEntry t.tab iU3 cols (if e == 0 then .bits0 else .bits1) col).getD {})
      (fun col => (planeEntry t.tab iU3 cols .pin col).getD {}) :=
  fun μ₀ entry hA =>
    k6_host_planes ρ e (cellM := fun m r c => μ₀ (cm m r c)) hm hk
      (fun p => zext μ₀ (placeOf mk pl p))
      (fun r hr c hc => by
        show μ₀ (cm (h.NHf + 1 + 1) r c) = μ₀ (pl r c)
        rw [hcm r hr c hc])
      (H.worldOf ρ (fun j => μ₀ (mk j)) entry) hA

end

/-! ## At the carried record -/

/-- **The head's tables lie in the record.** s stands in the head's link, opened; it holds what the
head heard and the tables that the description's text makes of that and of the covered positions;
its record of the smallness test has the plan's matrices, their number and the plan's numbers of the
arrays, and the list of these tables. -/
structure TabsLie (h : Model.Head.Shape) (L : Model.Head.HL) (hp : Model.Head.HPlanH2) (s : S)
    (o : HeadOwn) (cov : Model.Head.Covered) (x : Model.Head.Heard) (t : Model.Head.Tables) :
    Prop where
  here : s.here = .head o
  opened : o.opened = true
  covered : s.covered h.T h.V = .ok cov
  heard : o.x = some x
  laid : o.t = some t
  made : ReadsQuiet.tables h L hp cov x = .ok t
  mats : o.tl.mats = hp.tl.mats
  funs : o.tl.funs = t.funs
  nm : o.tl.NM = hp.tl.NM
  ix : o.tl.ix = hp.tl.ix

/-- **Behind a yes of the block that makes and closes the head's list of tables, they lie so.** -/
theorem tabsLie_behind {P : ReadsQuiet.PH} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : (ReadsQuiet.head P).decide s rs gs = .ok s') :
    ∃ o cov x t, TabsLie P.h P.L P.hp s' o cov x t := by
  obtain ⟨a, cov, x, t, tl', _, hop, hcov, hx, ht, hc, rfl⟩ := ReadsQuiet.head_ok hd
  obtain ⟨_, e2, e3, e4, _, _, _, _, _, _, e11⟩ := ReadsQuiet.closed_fields hc
  exact ⟨{ a with t := some t, tl := tl' }, cov, x, t, rfl, hop, hcov, hx, rfl, ht, e4, e2, e3,
    e11⟩

/-- That block leaves what the lookup returned, in both its homes, and the ledger. -/
theorem readsQuiet_keeps {P : ReadsQuiet.PH} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : (ReadsQuiet.head P).decide s rs gs = .ok s') :
    s'.look? = s.look? ∧ s'.lookHeard? = s.lookHeard? ∧ s'.fork? = s.fork? := by
  obtain ⟨a, cov, x, t, tl', ha, _, _, _, _, _, rfl⟩ := ReadsQuiet.head_ok hd
  simp [S.look?, S.lookHeard?, S.fork?, ha]

/-- **The three clauses at the seat's own reader, at a record in which the tables lie.** The law of
the reads is asked at the record's own matrices and list of tables, at the width of the array iU3 in
the record's ledger. htr, hK0: that array is there, with a column: the seat's reader refuses else.
-/
theorem k6_host_planes_at {K : Type} [CommRing K] (ρ : Reading K) {h : Model.Head.Shape}
    {L : Model.Head.HL} {hp : Model.Head.HPlanH2} {s : S} {o : HeadOwn} {cov : Model.Head.Covered}
    {x : Model.Head.Heard} {t : Model.Head.Tables} (Z : TabsLie h L hp s o cov x t) (iU3 : Nat)
    {tr : HTree} (htr : o.F.trees[iU3]? = some tr) (hK0 : tr.K ≠ 0)
    {cellM : Nat → Nat → Nat → K}
    (hm : (hp.tl.mats.getD (h.NHf + 1 + 1) {}).m / 2 ^ h.lmbH = 1)
    (hk : planeCols x.g1.shape h.lmbH ≤ (hp.tl.mats.getD (h.NHf + 1 + 1) {}).k)
    (ν : _root_.Fo.Pl → K)
    (h4 : ∀ r < 2 ^ h.lmbH, ∀ c < planeCols x.g1.shape h.lmbH,
      cellM (h.NHf + 1 + 1) r c = ν (.cell r c))
    (W : World K)
    (hA : ReadsAll ρ o.tl.mats o.tl.funs W.entry iU3 tr.K cellM) :
    ∃ r, callerReaders (planesAt iU3) s = some r ∧
      K3HostPlanes x.g1.shape h.lmbH (rdL ρ x.g1.zb0) (rdL ρ x.g1.zb1) ν (fun f => f.value ρ W)
        (fun e col => (r.1 e col).getD {}) (fun col => (r.2 col).getD {}) := by
  have hF : s.fork? = some o.F := by simp [S.fork?, Z.here, Z.opened]
  have eK : ((o.F.trees[iU3]?).map (·.K)).getD 1 = tr.K := by
    rw [htr]
    rfl
  rw [Z.mats, Z.funs, ← eK] at hA
  exact ⟨_, planesAt_readers iU3 Z.here hF Z.laid htr hK0,
    k6_host_planes ρ Z.made hm hk ν h4 W hA⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.tables_asks
#print axioms VerifiableInference.Desc.Kinds.Head.Law.tables_planes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_host_planes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_host_underReads
#print axioms VerifiableInference.Desc.Kinds.Head.Law.tabsLie_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.readsQuiet_keeps
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_host_planes_at
