-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoReadsLayer.lean.
The layers' sub-proof: the law of the reads at the three tables of its lookup's planes, from the law
at all its tables.

Layer.hearOwn (OnBytes/Model/Layer.lean) lays the families of tables by Layer.layTables, at the list
Layer.tableAsks, whose last three are the tables of the planes' matrix, and gives them their weights
by Layer.funsOf.

States:
  lay_find: in what Layer.layTables makes of a list of families, a family of one part whose name no
    earlier family has is found under its name at its first entry, and stands among the parts laid
    with that entry.
  funs_mem: what Layer.funsOf makes holds, for each family of one part laid, its table: with the
    family's matrix, rows and first entry, in the vector of reads, under the weights that
    Layer.phiOf gives.
  ask_name: no family before the last three has one of their names.
  own_tables: what Layer.hearOwn returns: its places of the families and its list of tables are what
    these two functions make of the group's list of families, the second at some list pt of named
    points, which is left open (the weights of the planes' three tables do not read it).
  layer_planeTabs: so, where the lookup's record holds the flat function's end values (Fo.HeardIs),
    the three tables are tables of the lookup's planes (Fo.PlaneTab,
    OnBytes/Tie/Pv/Lookup/Ends/FoReadsIn.lean) among o.funs, at the first entries that o.v.tabAt
    finds under their names.
  layer_readsLaw: and the law of the reads at all of o.funs (Fo.ReadsAll) gives Fo.ReadsLaw at these
    first entries.
Premises on public numbers, at any list of matrices mats: the planes' matrix has its rows in one
block of 2^lmb, and at least the planes' columns. On the cells: the cells of the planes' matrix are
the lookup's cells under ν.
Limits: Fo.ReadsAll is a hypothesis on the world: that any world meets it at o.funs is not shown.
That the three tables lie one behind the other is not said.
Not claimed: anything on soundness, completeness or hiding. Nor is it claimed that a run returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoReadsIn
import OnBytes.Tie.Pv.Lookup.Forest.FoPhi
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedLook
import OnBytes.Tie.Pv.Lookup.Port.FoHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV Finset OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Model.Layer Cb.Fo

/-- A family of one part is found under its name, and stands among the parts laid. -/
theorem lay_find (mats : Array (ℕ × ℕ)) (a : TableAsk) (ha : a.parts = 1) :
    ∀ (pre post : List TableAsk) (p : ℕ) (tab : List TableAt)
      (laid : List (TableAsk × List (ℕ × ℕ))) (n : ℕ),
      (∀ b ∈ pre, b.name ≠ a.name) →
      layTables mats (pre ++ a :: post) p = some (tab, laid, n) →
      ∃ p0, (tab.find? fun t => t.name == a.name).map (·.first) = some p0 ∧
        (a, [(a.M0, p0)]) ∈ laid
  | [], post, p, tab, laid, n, _, h => by
    rw [List.nil_append] at h
    unfold layTables at h
    dsimp only at h
    split at h
    · cases h
    · cases hr : layTables mats post (layParts mats a a.parts p).2 with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        have e := Option.some.inj h
        obtain ⟨e1, e2⟩ := Prod.mk.inj e
        obtain ⟨e2, _⟩ := Prod.mk.inj e2
        refine ⟨p, ?_, ?_⟩
        · rw [← e1, List.find?_cons_of_pos (by simp)]
          rfl
        · rw [← e2, ha]
          have : (layParts mats a 1 p).1 = [(a.M0, p)] := by
            simp [layParts, ha]
          rw [this]
          exact List.mem_cons_self
  | b :: pre, post, p, tab, laid, n, hn, h => by
    rw [List.cons_append] at h
    unfold layTables at h
    dsimp only at h
    split at h
    · cases h
    · cases hr : layTables mats (pre ++ a :: post) (layParts mats b b.parts p).2 with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        have e := Option.some.inj h
        obtain ⟨e1, e2⟩ := Prod.mk.inj e
        obtain ⟨e2, _⟩ := Prod.mk.inj e2
        obtain ⟨p0, q1, q2⟩ := lay_find mats a ha pre post _ r.1 r.2.1 r.2.2
          (fun x hx => hn x (List.mem_cons_of_mem _ hx)) hr
        refine ⟨p0, ?_, ?_⟩
        · rw [← e1, List.find?_cons_of_neg (by simpa using hn b List.mem_cons_self)]
          exact q1
        · rw [← e2]
          exact List.mem_cons_of_mem _ q2

/-- Each member of a list has its image in what mapM returns. -/
theorem mapM_mem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → ∀ a ∈ l, ∃ b ∈ r, f a = some b
  | [], _, _, a, ha => absurd ha List.not_mem_nil
  | x :: l, r, h, a, ha => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => rw [hx] at h; cases h
    | some b =>
      rw [hx] at h
      cases hl : l.mapM f with
      | none => rw [hl] at h; cases h
      | some bs =>
        rw [hl] at h
        have e : b :: bs = r := Option.some.inj h
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact ⟨b, by rw [← e]; exact List.mem_cons_self, hx⟩
        · obtain ⟨b', m1, m2⟩ := mapM_mem f l bs hl a ha'
          exact ⟨b', by rw [← e]; exact List.mem_cons_of_mem _ m1, m2⟩

/-- The tables of one family laid. -/
def famFuns (y : Lay) (fo : Forest.Heard) (pt : List (String × Array E))
    (x : TableAsk × List (ℕ × ℕ)) : Option (List HFun) := do
  let phi ← phiOf y fo pt x.1
  pure (x.2.map fun m => ({ mat := m.1, len := x.1.L, phi, tree := 2, start := m.2 } : HFun))

/-- The table of a family of one part. -/
theorem funs_mem (y : Lay) (fo : Forest.Heard) (pt : List (String × Array E))
    (laid : List (TableAsk × List (ℕ × ℕ))) (funs : Array HFun)
    (h : funsOf y fo pt laid = some funs) (a : TableAsk) (M p0 : ℕ)
    (hm : (a, [(M, p0)]) ∈ laid) :
    ∃ phi, phiOf y fo pt a = some phi ∧
      ({ mat := M, len := a.L, phi := phi, tree := 2, start := p0 } : HFun) ∈ funs.toList := by
  have h' : (laid.mapM (famFuns y fo pt)).bind (fun l => some l.flatten.toArray) = some funs := h
  cases hl : laid.mapM (famFuns y fo pt) with
  | none => rw [hl] at h'; cases h'
  | some l =>
    rw [hl] at h'
    have e : l.flatten.toArray = funs := Option.some.inj h'
    obtain ⟨z, hz, hq⟩ := mapM_mem _ _ _ hl _ hm
    unfold famFuns at hq
    cases hp : phiOf y fo pt a with
    | none =>
      rw [show phiOf y fo pt (a, [(M, p0)]).1 = none from hp] at hq
      cases hq
    | some phi =>
      rw [show phiOf y fo pt (a, [(M, p0)]).1 = some phi from hp] at hq
      have ez : [({ mat := M, len := a.L, phi := phi, tree := 2, start := p0 } : HFun)] = z :=
        Option.some.inj hq
      refine ⟨phi, rfl, ?_⟩
      rw [← e]
      exact List.mem_flatten.mpr ⟨z, hz, by rw [← ez]; exact List.mem_cons_self⟩

/-- The families of one matrix at a list of points. -/
def famAsks (y : Lay) (mn : String) (M0 parts : ℕ) (pts : List String) (lng : Bool) :
    List TableAsk :=
  pts.map fun n => ⟨mn ++ "@" ++ n, M0, parts, if lng then 2 ^ y.h.la else y.T, n, lng⟩

/-- The families before the three of the planes' matrix. -/
def preAsks (y : Lay) (rd : Reads) (g : ℕ) : List TableAsk :=
  famAsks y "af" (matIx y).iAF (y.parts.getD 0 0) rd.rdAF true ++
  famAsks y "qa" (matIx y).iQA 1 rd.rdQA true ++
  famAsks y "xbI" (matIx y).iXI 1 rd.rdXI true ++
  (if g == 0 then famAsks y "xbI" (matIx y).iXI 1 ["Z_E"] true else []) ++
  famAsks y "xbO" (matIx y).iXO 1 rd.rdXO true ++
  famAsks y "ad" (matIx y).iAD (y.parts.getD 1 0) rd.rdAD false ++
  famAsks y "ar" (matIx y).iAR 1 rd.rdAR false ++
  (if y.h.p4 then famAsks y "qa" (matIx y).iQA 1 rd.rdQS false else [])

/-- One of the three families of the planes' matrix. -/
def planeAsk (y : Lay) (name : String) : TableAsk := ⟨name, (matIx y).iB, 1, 2 ^ y.h.lmb, "", false⟩

theorem tableAsks_eq (y : Lay) (rd : Reads) (g : ℕ) :
    tableAsks y rd g = preAsks y rd g ++
      [planeAsk y "b-bits-0", planeAsk y "b-bits-1", planeAsk y "b-pin"] := rfl

/-- The first sign of the name of a family before the last three is not b. -/
theorem fam_head {y : Lay} {mn : String} {M0 parts : ℕ} {pts : List String} {lng : Bool}
    {b : TableAsk} (hb : b ∈ famAsks y mn M0 parts pts lng) :
    b.name.toList.head? = (mn.toList ++ ['@']).head? := by
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hb
  show (mn ++ "@" ++ n).toList.head? = _
  rw [String.toList_append, String.toList_append]
  show ((mn.toList ++ ['@']) ++ n.toList).head? = _
  rw [List.head?_append]
  cases hh : (mn.toList ++ ['@']).head? with
  | none => simp at hh
  | some c => rfl

theorem ask_name {y : Lay} {rd : Reads} {g : ℕ} {b : TableAsk} (hb : b ∈ preAsks y rd g) :
    b.name.toList.head? ≠ some 'b' := by
  unfold preAsks at hb
  simp only [List.mem_append] at hb
  rcases hb with ((((((hb | hb) | hb) | hb) | hb) | hb) | hb) | hb
  · rw [fam_head hb]; decide
  · rw [fam_head hb]; decide
  · rw [fam_head hb]; decide
  · split at hb
    · rw [fam_head hb]; decide
    · exact absurd hb List.not_mem_nil
  · rw [fam_head hb]; decide
  · rw [fam_head hb]; decide
  · rw [fam_head hb]; decide
  · split at hb
    · rw [fam_head hb]; decide
    · exact absurd hb List.not_mem_nil

theorem ask_ne {y : Lay} {rd : Reads} {g : ℕ} {b : TableAsk} (hb : b ∈ preAsks y rd g)
    (nm : String) (hn : nm.toList.head? = some 'b') : b.name ≠ nm := fun e =>
  ask_name hb (by rw [e]; exact hn)

/-- What Layer.hearOwn returns: its places of the families and its list of tables. -/
theorem own_tables (P : Layer.Pub) (hp : Layer.HPlan2) (g : ℕ) (fo : Forest.Heard) :
    Yields (Layer.hearOwn P hp g fo) fun o =>
      o.v.y = P.y ∧ ∃ laid n pt,
        layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) (tableAsks P.y P.rd g) 0 =
          some (o.v.tab, laid, n) ∧
        funsOf P.y fo pt laid = some o.funs := by
  unfold Layer.hearOwn
  simp only []
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind2 (p := fun x => layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k))
    (tableAsks P.y P.rd g) 0 = some x) (fun F c a G c' hr => ?_) fun x hx => ?_
  · obtain ⟨a', h1, e⟩ := (get_ok _ _ _ _).1 hr
    have ea : a = a' := congrArg (fun z : (_ × Fork) × Ctx => z.1.1) e
    rw [h1, ea]
  obtain ⟨tab, laid, nU3⟩ := x
  dsimp only
  repeat' first
    | (refine Yields.bind2 (p := fun f : Array HFun => ∃ pt, funsOf P.y fo pt laid = some f)
        (fun F c a G c' hr => ?_) (fun f hf => ?_))
    | (refine Yields.bind fun _ => ?_)
    | split
  all_goals first
    | (obtain ⟨a', h1, e⟩ := (get_ok _ _ _ _).1 hr
       have ea : a = a' := congrArg (fun z : (_ × Fork) × Ctx => z.1.1) e
       exact ⟨_, by rw [h1, ea]⟩)
    | (obtain ⟨pt, hpt⟩ := hf
       exact Yields.pure ⟨rfl, laid, nU3, pt, hx, hpt⟩)

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- One of the three tables of the planes at the layers. -/
theorem layer_planeTab {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)}
    {mats' : Array (ℕ × ℕ)} {pre post : List TableAsk} {tab : List TableAt}
    {laid : List (TableAsk × List (ℕ × ℕ))} {n : ℕ} {funs : Array HFun} (nm : String)
    (hl : layTables mats' (pre ++ planeAsk y nm :: post) 0 = some (tab, laid, n))
    (hn : ∀ b ∈ pre, b.name ≠ nm) (hf : funsOf y fo pt laid = some funs) (phi : Array E)
    (hp : phiOf y fo pt (planeAsk y nm) = some phi) (mats : Array TMat)
    (cellM : ℕ → ℕ → ℕ → K) (w : ℕ → K) (h : FoNums.Sh) (ν : Pl → K)
    (h1 : (mats.getD (matIx y).iB {}).m / 2 ^ y.h.lmb = 1)
    (h2 : planeCols h y.h.lmb ≤ (mats.getD (matIx y).iB {}).k)
    (h3 : ∀ j < 2 ^ y.h.lmb, ρ.val (phi.getD j zeroE) = w j)
    (h4 : ∀ r < 2 ^ y.h.lmb, ∀ c < planeCols h y.h.lmb, cellM (matIx y).iB r c = ν (.cell r c)) :
    ∃ p0 f, (tab.find? fun t => t.name == nm).map (·.first) = some p0 ∧
      PlaneTab ρ mats funs cellM f p0 w h y.h.lmb ν := by
  obtain ⟨p0, q1, q2⟩ := lay_find mats' (planeAsk y nm) rfl pre post 0 tab laid n hn hl
  obtain ⟨phi', e1, e2⟩ := funs_mem y fo pt laid funs hf (planeAsk y nm) _ p0 q2
  obtain rfl : phi = phi' := Option.some.inj (hp.symm.trans e1)
  exact ⟨p0, _, q1, e2, rfl, rfl, rfl, h1, h2, h3, h4⟩

/-- The three tables of the planes at the layers. -/
theorem layer_planeTabs (P : Layer.Pub) (hp : Layer.HPlan2) (g : ℕ) (fo : Forest.Heard)
    (F G : Fork) (c c' : Ctx) (o : Layer.Own)
    (hh : Layer.hearOwn P hp g fo F c = .ok ((o, G), c')) (F0 : Fork) (jLK : ℕ) (rsK : Rounds K)
    (hI : HeardIs ρ o.H.fo F0 (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK)) (mats : Array TMat)
    (cellM : ℕ → ℕ → ℕ → K) (ν : Pl → K)
    (h1 : (mats.getD (matIx o.v.y).iB {}).m / 2 ^ o.v.y.h.lmb = 1)
    (h2 : planeCols o.H.fo.shape o.v.y.h.lmb ≤ (mats.getD (matIx o.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellM (matIx o.v.y).iB r c = ν (.cell r c)) :
    ∃ tB0 tB1 tP f0 f1 fP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      PlaneTab ρ mats o.funs cellM f0 tB0
        (fun r => (phiBK o.H.fo.shape o.v.y.h.lmb
          (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).zb0).getD r 0) o.H.fo.shape o.v.y.h.lmb ν ∧
      PlaneTab ρ mats o.funs cellM f1 tB1
        (fun r => (phiBK o.H.fo.shape o.v.y.h.lmb
          (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).zb1).getD r 0) o.H.fo.shape o.v.y.h.lmb ν ∧
      PlaneTab ρ mats o.funs cellM fP tP (fun r => (2 : K) ^ (r % 32)) o.H.fo.shape
        o.v.y.h.lmb ν := by
  obtain ⟨ey, laid, n, pt, hl, hf⟩ := own_tables P hp g fo _ _ _ _ _ hh
  have efo : o.H.fo = fo := g_own_fo P hp g fo _ _ _ _ _ hh
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
  -- the weights of the two tables of bits are there: Layer.funsOf has returned
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
    (fun r => (phiBK o.H.fo.shape o.v.y.h.lmb
      (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).zb0).getD r 0) o.H.fo.shape ν h1 h2
    (fun j _ => by
      rw [rdL_getD, phiB_val ρ o.H.fo o.v.y.h.lmb 0 b0 y0, ← show rdL ρ o.H.fo.zb0 = _ from hI.zb0]
      rfl) h4
  obtain ⟨tB1, f1, a1, T1⟩ := layer_planeTab ρ "b-bits-1" hl1
    (fun b hb => by
      rcases List.mem_append.mp hb with hb | hb
      · exact ask_ne hb "b-bits-1" (by decide)
      · rw [List.mem_singleton.mp hb]
        show "b-bits-0" ≠ "b-bits-1"
        decide) hf b1 z1 mats cellM
    (fun r => (phiBK o.H.fo.shape o.v.y.h.lmb
      (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).zb1).getD r 0) o.H.fo.shape ν h1 h2
    (fun j _ => by
      rw [rdL_getD, phiB_val ρ o.H.fo o.v.y.h.lmb 1 b1 y1, ← show rdL ρ o.H.fo.zb1 = _ from hI.zb1]
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

/-- The law of the reads at the planes' three tables of the layers. -/
theorem layer_readsLaw (P : Layer.Pub) (hp : Layer.HPlan2) (g : ℕ) (fo : Forest.Heard)
    (F G : Fork) (c c' : Ctx) (o : Layer.Own)
    (hh : Layer.hearOwn P hp g fo F c = .ok ((o, G), c')) (F0 : Fork) (jLK : ℕ) (rsK : Rounds K)
    (hI : HeardIs ρ o.H.fo F0 (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK)) (mats : Array TMat)
    (cellM : ℕ → ℕ → ℕ → K) (ν : Pl → K)
    (h1 : (mats.getD (matIx o.v.y).iB {}).m / 2 ^ o.v.y.h.lmb = 1)
    (h2 : planeCols o.H.fo.shape o.v.y.h.lmb ≤ (mats.getD (matIx o.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellM (matIx o.v.y).iB r c = ν (.cell r c))
    (entry : ℕ → ℕ → ℕ → K) (iU3 K3 : ℕ) (hA : ReadsAll ρ mats o.funs entry iU3 K3 cellM)
    (tB0 tB1 tP : ℕ) (t0 : o.v.tabAt "b-bits-0" = some tB0) (t1 : o.v.tabAt "b-bits-1" = some tB1)
    (t2 : o.v.tabAt "b-pin" = some tP) :
    ReadsLaw o.H.fo.shape o.v.y.h.lmb (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).zb0
      (endsOf o.H.fo.shape o.v.y.h.lmb jLK rsK).zb1 ν entry iU3 K3 tB0 tB1 tP := by
  obtain ⟨tB0', tB1', tP', f0, f1, fP, a0, a1, a2, T0, T1, TP⟩ :=
    layer_planeTabs ρ P hp g fo F G c c' o hh F0 jLK rsK hI mats cellM ν h1 h2 h4
  obtain rfl : tB0' = tB0 := Option.some.inj (a0.symm.trans t0)
  obtain rfl : tB1' = tB1 := Option.some.inj (a1.symm.trans t1)
  obtain rfl : tP' = tP := Option.some.inj (a2.symm.trans t2)
  exact readsLaw_of_readsAll ρ hA T0 T1 TP

end
end Fo
