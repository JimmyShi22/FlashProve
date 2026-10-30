-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PlanesHost.lean: the layers' debt to the lookup on the planes of its counts, under
the law of the reads, from runs of the layers' own plain text.

Johnson/Meaning/PlanesForms.lean shows that under the law of the rows alone the layers' forms are
not worth what the lookup's claims need. What lacks is the law of the reads (Fo.ReadsAll,
OnBytes/Tie/Pv/Lookup/Ends/FoKeys.lean): each entry of a table in the vector of reads is the
combination of its matrix's cells under the table's weights. The library has the step from there to
the planes' three tables (Fo.layer_readsLaw, Ends/FoReadsLayer.lean), on a run of the routine
Layer.hearOwn, of which it spends two equations and the lookup's record. Here these come off a run
of the layers' plain hearing, and the library's lemmas on plain data are called; no theorem on a run
of a routine in a context is called.

The three clauses (`K3HostPlanes`) and the law for all callers: Johnson/Meaning/PlanesLaw.lean.

Main names (namespace `Meaning.Planes`).
  `hear_tables`: what a run of `hearFl` leaves: the layout; the lookup's record; the places of the
      families of tables and the list of tables are what layTables and funsOf make.
  `k4_planeTabs`: so the three tables of the planes stand among o.funs (Fo.PlaneTab).
  `k4_readsLaw`: the law of the reads at all of o.funs gives Fo.ReadsLaw at the three first entries.
  `forms_there`: where `planesParts` is there, the layers have a form for every column.
  `k4_host_planes`: **the three clauses at the layers' forms, in any world with the law of the
      reads**: the law for all callers at the layers' letters.
  `k4_readers`: the layers' forms are entries of the vector of reads, at every column.
  `k4_host_underReads`: K3HostPlanesUnderReads at the layers' forms.

Premises that nobody pays here: zb0 and zb1 are what the lookup's two heard points read as: whoever
spends the clauses owes that these are the points at which the lookup's claims are judged (the
fields zb0 and zb1 of Fo.HeardIs); the planes' matrix has its rows in one block of 2^lmb and at
least the planes' columns; its cells are the lookup's cells; THE LAW OF THE READS. Limits. Ties in
one world: no draw, no error term, nothing on soundness. The calling kind's debt on its key forms is
not treated. That entries meet the law of the reads, at any cells: Johnson/Meaning/PlanesMeet.lean.
The two public premises: Johnson/Meaning/PlanesNumbers.lean.
-/
import Johnson.Meaning.PlanesForms
import Johnson.Meaning.PlanesLaw
import Johnson.Meaning.PlanesTie
import Johnson.Meaning.HKTHear
import OnBytes.Tie.Pv.Lookup.Ends.FoReadsLayer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Planes
open Finset
open Cb Cb.Fo Cb.Fo.NumsEq TwV
open OnBytes OnBytes.Model Fo
open Cb.Fo.Pin
open OnBytes.Model.Layer (Env Lay Heard Pub Own HPlan2 layTables tableAsks funsOf matIx)
open OnBytes.K.Kc
open OnBytes.Desc.First.K4 (engFl hearFl hear hearTerms hearNorms)
open Meaning.HKT (bind_some pure_some need_some hear_cut)
open OnBytes.Road.Rows (planesL planesAtO countO planeFormsO planeCol)

/-! ## What a run of the hearing leaves -/

theorem need_val {α : Type} {x : Option α} {a : α} {F G : Fork} {t u : Tape}
    (h : Fl.need x F t = some (a, G, u)) : x = some a := by
  unfold Fl.need at h
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  rw [hb, e.1]

theorem hearTerms_fo {P : Pub} {H H' : Heard} {F F' : Fork} {t t' : Tape}
    (h : hearTerms engFl P H F t = some (H', F', t')) : H'.fo = H.fo := by
  unfold hearTerms at h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  obtain ⟨⟨_, _⟩, _, _, _, h⟩ := bind_some h
  rw [pure_some h]

theorem hearNorms_fo {P : Pub} {g : ℕ} {fo : Forest.Heard} {H : Heard} {F F' : Fork} {t t' : Tape}
    (h : hearNorms engFl P g fo F t = some (H, F', t')) : H.fo = fo := by
  unfold hearNorms at h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  dsimp only at h
  split at h <;>
  · obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    rw [pure_some h]

/-- **What a run of the layers' plain hearing leaves on the tables.** -/
theorem hear_tables {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (h : hearFl P hp g fo F t = some (o, F', t')) :
    o.v.y = P.y ∧ o.H.fo = fo ∧ ∃ laid n pt,
      layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) (tableAsks P.y P.rd g) 0 =
        some (o.v.tab, laid, n) ∧
      funsOf P.y fo pt laid = some o.funs := by
  have hfo : o.H.fo = fo := by
    obtain ⟨H0, _, _, _, _, hN, hT⟩ := hear_cut h
    rw [hearTerms_fo hT, hearNorms_fo hN]
  refine ⟨?_, hfo, ?_⟩
  all_goals
    unfold hearFl hear at h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨iU3, _, _, _, h⟩ := bind_some h
    obtain ⟨H0, _, _, _, h⟩ := bind_some h
    obtain ⟨H, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨⟨tab, laid, nU3⟩, _, _, hl, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨K, _, _, _, h⟩ := bind_some h
    obtain ⟨⟨hd, hd2⟩, _, _, _, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨claimsP, _, _, _, h⟩ := bind_some h
    split at h <;>
    · obtain ⟨_, _, _, _, h⟩ := bind_some h
      obtain ⟨_, _, _, _, h⟩ := bind_some h
      obtain ⟨_, _, _, _, h⟩ := bind_some h
      obtain ⟨_, _, _, _, h⟩ := bind_some h
      obtain ⟨pt, _, _, _, h⟩ := bind_some h
      obtain ⟨funs, _, _, hf, h⟩ := bind_some h
      rw [pure_some h]
      try exact ⟨laid, nU3, pt, need_val hl, need_val hf⟩

/-! ## The three tables of the planes -/

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- **The three tables of the planes stand among the tables that the hearing leaves**, with the
weights of the two heard points and the powers of two. After the library's Fo.layer_planeTabs, whose
steps on plain data are called here one by one. -/
theorem k4_planeTabs {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : hearFl P hp g fo F t = some (o, F', t')) (zb0 zb1 : List K)
    (hz0 : rdL ρ o.H.fo.zb0 = zb0) (hz1 : rdL ρ o.H.fo.zb1 = zb1) (mats : Array TMat)
    (cellM : ℕ → ℕ → ℕ → K) (ν : _root_.Fo.Pl → K)
    (h1 : (mats.getD (matIx o.v.y).iB {}).m / 2 ^ o.v.y.h.lmb = 1)
    (h2 : planeCols o.H.fo.shape o.v.y.h.lmb ≤ (mats.getD (matIx o.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellM (matIx o.v.y).iB r c = ν (.cell r c)) :
    ∃ tB0 tB1 tP f0 f1 fP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      PlaneTab ρ mats o.funs cellM f0 tB0
        (fun r => (phiBK o.H.fo.shape o.v.y.h.lmb zb0).getD r 0) o.H.fo.shape o.v.y.h.lmb ν ∧
      PlaneTab ρ mats o.funs cellM f1 tB1
        (fun r => (phiBK o.H.fo.shape o.v.y.h.lmb zb1).getD r 0) o.H.fo.shape o.v.y.h.lmb ν ∧
      PlaneTab ρ mats o.funs cellM fP tP (fun r => (2 : K) ^ (r % 32)) o.H.fo.shape
        o.v.y.h.lmb ν := by
  obtain ⟨ey, efo, laid, n, pt, hl, hf⟩ := hear_tables hh
  rw [← ey, ← efo] at hf
  rw [← ey, tableAsks_eq] at hl
  have hl1 : layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k))
      ((preAsks o.v.y P.rd g ++ [planeAsk o.v.y "b-bits-0"]) ++ planeAsk o.v.y "b-bits-1" ::
        [planeAsk o.v.y "b-pin"]) 0 = some (o.v.tab, laid, n) := by
    rw [List.append_assoc]
    exact hl
  have hl2 : layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k))
      ((preAsks o.v.y P.rd g ++ [planeAsk o.v.y "b-bits-0", planeAsk o.v.y "b-bits-1"]) ++
        planeAsk o.v.y "b-pin" :: []) 0 = some (o.v.tab, laid, n) := by
    rw [List.append_assoc]
    exact hl
  obtain ⟨_, _, q0⟩ := lay_find _ (planeAsk o.v.y "b-bits-0") rfl _ _ 0 _ _ _
    (fun b hb => ask_ne hb "b-bits-0" (by decide)) hl
  obtain ⟨b0, z0, _⟩ := funs_mem _ _ _ _ _ hf _ _ _ q0
  obtain ⟨_, _, q1⟩ := lay_find _ (planeAsk o.v.y "b-bits-1") rfl _ _ 0 _ _ _
    (fun b hb => by
      rcases List.mem_append.mp hb with hb | hb
      · exact ask_ne hb "b-bits-1" (by decide)
      · rw [List.mem_singleton.mp hb]
        show "b-bits-0" ≠ "b-bits-1"
        decide) hl1
  obtain ⟨b1, z1, _⟩ := funs_mem _ _ _ _ _ hf _ _ _ q1
  have y0 : Forest.phiB o.H.fo o.v.y.h.lmb 0 = some b0 := z0
  have y1 : Forest.phiB o.H.fo o.v.y.h.lmb 1 = some b1 := z1
  obtain ⟨tB0, f0, a0, T0⟩ := layer_planeTab ρ "b-bits-0" hl
    (fun b hb => ask_ne hb "b-bits-0" (by decide)) hf b0 z0 mats cellM
    (fun r => (phiBK o.H.fo.shape o.v.y.h.lmb zb0).getD r 0) o.H.fo.shape ν h1 h2
    (fun j _ => by
      rw [rdL_getD, phiB_val ρ o.H.fo o.v.y.h.lmb 0 b0 y0, ← hz0]
      rfl) h4
  obtain ⟨tB1, f1, a1, T1⟩ := layer_planeTab ρ "b-bits-1" hl1
    (fun b hb => by
      rcases List.mem_append.mp hb with hb | hb
      · exact ask_ne hb "b-bits-1" (by decide)
      · rw [List.mem_singleton.mp hb]
        show "b-bits-0" ≠ "b-bits-1"
        decide) hf b1 z1 mats cellM
    (fun r => (phiBK o.H.fo.shape o.v.y.h.lmb zb1).getD r 0) o.H.fo.shape ν h1 h2
    (fun j _ => by
      rw [rdL_getD, phiB_val ρ o.H.fo o.v.y.h.lmb 1 b1 y1, ← hz1]
      rfl) h4
  obtain ⟨tP, fP, a2, TP⟩ := layer_planeTab ρ "b-pin" hl2
    (fun b hb => by
      rcases List.mem_append.mp hb with hb | hb
      · exact ask_ne hb "b-pin" (by decide)
      · rcases List.mem_cons.mp hb with rfl | hb
        · show "b-bits-0" ≠ "b-pin"
          decide
        · rw [List.mem_singleton.mp hb]
          show "b-bits-1" ≠ "b-pin"
          decide) hf (Forest.phiP o.v.y.h.lmb) rfl mats cellM _ o.H.fo.shape ν h1 h2
    (fun j hj => phiP_val ρ o.v.y.h.lmb j hj) h4
  exact ⟨tB0, tB1, tP, f0, f1, fP, a0, a1, a2, T0, T1, TP⟩

/-- **The law of the reads at all tables gives the law at the planes' three.** -/
theorem k4_readsLaw {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : hearFl P hp g fo F t = some (o, F', t')) (zb0 zb1 : List K)
    (hz0 : rdL ρ o.H.fo.zb0 = zb0) (hz1 : rdL ρ o.H.fo.zb1 = zb1) (mats : Array TMat)
    (cellM : ℕ → ℕ → ℕ → K) (ν : _root_.Fo.Pl → K)
    (h1 : (mats.getD (matIx o.v.y).iB {}).m / 2 ^ o.v.y.h.lmb = 1)
    (h2 : planeCols o.H.fo.shape o.v.y.h.lmb ≤ (mats.getD (matIx o.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellM (matIx o.v.y).iB r c = ν (.cell r c))
    (entry : ℕ → ℕ → ℕ → K) (iU3 K3 : ℕ) (hA : ReadsAll ρ mats o.funs entry iU3 K3 cellM) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      ReadsLaw o.H.fo.shape o.v.y.h.lmb zb0 zb1 ν entry iU3 K3 tB0 tB1 tP := by
  obtain ⟨tB0, tB1, tP, f0, f1, fP, a0, a1, a2, T0, T1, TP⟩ :=
    k4_planeTabs ρ hh zb0 zb1 hz0 hz1 mats cellM ν h1 h2 h4
  exact ⟨tB0, tB1, tP, a0, a1, a2, readsLaw_of_readsAll ρ hA T0 T1 TP⟩

/-! ## The layers have a form for every column -/

/-- A fold that asks a value at every member and returns has found a value at every member. -/
theorem foldlM_there {α β γ : Type} (p : α → Option γ) (k : β → α → γ → β) :
    ∀ (l : List α) (b r : β), l.foldlM (fun f a => (p a).bind fun x => some (k f a x)) b = some r →
      ∀ a ∈ l, ∃ x, p a = some x
  | [], _, _, _, a, ha => by cases ha
  | c :: l, b, r, h, a, ha => by
    rw [List.foldlM_cons] at h
    obtain ⟨b', hb, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.mp hb
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨x, hx⟩
    · exact foldlM_there p k l b' r h' a ha

/-- **Where the layers' three claims on the planes are there, the layers have a form for every
column of the planes' matrix**, in each of the three tables. -/
theorem forms_there {v : Env} {fo : Forest.Heard} {pp : Aff × List Aff}
    (h : Desc.First.K4.planesParts v fo = some pp) :
    ∃ tB0 tB1 tP, v.tabAt "b-bits-0" = some tB0 ∧ v.tabAt "b-bits-1" = some tB1 ∧
      v.tabAt "b-pin" = some tP ∧
      ∀ col < fo.shape.NC * 2 ^ (fo.shape.kT + 5 - v.y.h.lmb),
        (∃ b, planeCol v tB0 col = some b) ∧ (∃ b, planeCol v tB1 col = some b) ∧
          ∃ b, planeCol v tP col = some b := by
  have hL := planesParts_planesL h
  unfold planesL planeFormsO at hL
  obtain ⟨tB0, a0, hL⟩ := Option.bind_eq_some_iff.mp hL
  obtain ⟨tB1, a1, hL⟩ := Option.bind_eq_some_iff.mp hL
  obtain ⟨tP, a2, hL⟩ := Option.bind_eq_some_iff.mp hL
  obtain ⟨rows, h3, _⟩ := Option.bind_eq_some_iff.mp hL
  obtain ⟨at0, c0, h3⟩ := Option.bind_eq_some_iff.mp h3
  obtain ⟨at1, c1, h3⟩ := Option.bind_eq_some_iff.mp h3
  obtain ⟨cnt, c2, _⟩ := Option.bind_eq_some_iff.mp h3
  refine ⟨tB0, tB1, tP, a0, a1, a2, fun col hc => ⟨?_, ?_, ?_⟩⟩
  · exact foldlM_there (fun col => planeCol v tB0 col) _ _ _ _ c0 col (List.mem_range.mpr hc)
  · exact foldlM_there (fun col => planeCol v tB1 col) _ _ _ _ c1 col (List.mem_range.mpr hc)
  · exact foldlM_there (fun col => planeCol v tP col) _ _ _ _ c2 col (List.mem_range.mpr hc)

/-- **The layers' readers of the planes' columns are entries of the vector of reads**, at every
column, where the layers' three claims on the planes are there. -/
theorem k4_readers {v : Env} {fo : Forest.Heard} {pp : Aff × List Aff}
    (h : Desc.First.K4.planesParts v fo = some pp) :
    ∃ tB0 tB1 tP, v.tabAt "b-bits-0" = some tB0 ∧ v.tabAt "b-bits-1" = some tB1 ∧
      v.tabAt "b-pin" = some tP ∧
      ReadersAre fo.shape v.y.h.lmb v.iU3 v.K3 tB0 tB1 tP (k4Bit v tB0 tB1) (k4Pin v tP) := by
  obtain ⟨tB0, tB1, tP, a0, a1, a2, hc⟩ := forms_there h
  refine ⟨tB0, tB1, tP, a0, a1, a2, ⟨fun col hcol => ?_, fun col hcol => ?_, fun col hcol => ?_⟩⟩
  · obtain ⟨⟨b, hb⟩, _, _⟩ := hc col hcol
    show (planeCol v tB0 col).getD {} = _
    rw [hb]
    exact planeCol_ent hb
  · obtain ⟨_, ⟨b, hb⟩, _⟩ := hc col hcol
    show (planeCol v tB1 col).getD {} = _
    rw [hb]
    exact planeCol_ent hb
  · obtain ⟨_, _, ⟨b, hb⟩⟩ := hc col hcol
    show (planeCol v tP col).getD {} = _
    rw [hb]
    exact planeCol_ent hb

/-! ## The debt, paid under the law of the reads -/

/-- **The three clauses of the host's law on the planes, at the layers' forms**, in any world that
meets the law of the reads at the tables that the hearing left. hh: the hearing's run. hq: the
layers' three claims on the planes are there (a run of formsFrontWith gives it). -/
theorem k4_host_planes {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : hearFl P hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (zb0 zb1 : List K) (hz0 : rdL ρ o.H.fo.zb0 = zb0) (hz1 : rdL ρ o.H.fo.zb1 = zb1)
    (mats : Array TMat) (cellM : ℕ → ℕ → ℕ → K) (ν : _root_.Fo.Pl → K)
    (h1 : (mats.getD (matIx o.v.y).iB {}).m / 2 ^ o.v.y.h.lmb = 1)
    (h2 : planeCols o.H.fo.shape o.v.y.h.lmb ≤ (mats.getD (matIx o.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellM (matIx o.v.y).iB r c = ν (.cell r c))
    (W : World K) (hA : ReadsAll ρ mats o.funs W.entry o.v.iU3 o.v.K3 cellM) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb zb0 zb1 ν (fun f => f.value ρ W)
        (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨tB0, tB1, tP, f0, f1, fP, a0, a1, a2, T0, T1, TP⟩ :=
    k4_planeTabs ρ hh zb0 zb1 hz0 hz1 mats cellM ν h1 h2 h4
  obtain ⟨tB0', tB1', tP', b0, b1, b2, R⟩ := k4_readers hq
  obtain rfl : tB0' = tB0 := Option.some.inj (b0.symm.trans a0)
  obtain rfl : tB1' = tB1 := Option.some.inj (b1.symm.trans a1)
  obtain rfl : tP' = tP := Option.some.inj (b2.symm.trans a2)
  exact ⟨tB0', tB1', tP', a0, a1, a2, host_planes ρ T0 T1 TP R W hA⟩

/-- **The three clauses at the layers' forms, for all cells and all entries that meet the law of the
reads.** cm: where the matrices' cells lie; hcm: the cells of the planes' matrix lie where the
lookup's do. -/
theorem k4_host_underReads {J₀ : Type} {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard}
    {F F' : Fork} {t t' : Tape} {o : Own} (hh : hearFl P hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (zb0 zb1 : List K) (hz0 : rdL ρ o.H.fo.zb0 = zb0) (hz1 : rdL ρ o.H.fo.zb1 = zb1)
    (mats : Array TMat)
    (h1 : (mats.getD (matIx o.v.y).iB {}).m / 2 ^ o.v.y.h.lmb = 1)
    (h2 : planeCols o.H.fo.shape o.v.y.h.lmb ≤ (mats.getD (matIx o.v.y).iB {}).k)
    (H : Fork) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (cm : ℕ → ℕ → ℕ → J₀)
    (hcm : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cm (matIx o.v.y).iB r c = pl r c) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanesUnderReads ρ H o.H.fo.shape o.v.y.h.lmb zb0 zb1 mk pl mats o.funs o.v.iU3
        o.v.K3 cm (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨tB0, tB1, tP, b0, b1, b2, _⟩ := forms_there hq
  refine ⟨tB0, tB1, tP, b0, b1, b2, fun μ₀ entry hA => ?_⟩
  obtain ⟨tB0', tB1', tP', a0, a1, a2, X⟩ :=
    k4_host_planes ρ hh hq zb0 zb1 hz0 hz1 mats (fun m r c => μ₀ (cm m r c))
      (fun p => zext μ₀ (placeOf mk pl p)) h1 h2
      (fun r hr c hc => by
        show μ₀ (cm (matIx o.v.y).iB r c) = μ₀ (pl r c)
        rw [hcm r hr c hc])
      (H.worldOf ρ (fun j => μ₀ (mk j)) entry) hA
  obtain rfl : tB0' = tB0 := Option.some.inj (a0.symm.trans b0)
  obtain rfl : tB1' = tB1 := Option.some.inj (a1.symm.trans b1)
  obtain rfl : tP' = tP := Option.some.inj (a2.symm.trans b2)
  exact X

end

#print axioms forms_there
#print axioms k4_readers
#print axioms k4_host_planes
#print axioms k4_host_underReads
#print axioms hear_tables
#print axioms k4_planeTabs
#print axioms k4_readsLaw

end Meaning.Planes
