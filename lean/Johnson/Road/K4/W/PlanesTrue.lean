-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/PlanesTrue.lean: CONDITIONAL.

Not shown here. THAT THE LOOKUP's THREE CLAIMS ON ITS PLANES HOLD AT ν (K3Planes), and that some
rounds rs are what the lookup has heard (hI): hypotheses, AND THE WEIGHT LIES ON THESE TWO: ν is a
free letter, so that the planes' matrix in Mm holds ν's cells (h4) and that the mask row is ν's (hm)
can be met by make, by laying ν so. That the planes' matrix has its rows in one run (h1) and at
least the planes' columns (h2): public hypotheses. Hypotheses besides, none shown here: the public
facts on the layout (K4Ground); that the run "front" returns (hfr) and the text planesParts (hpp);
that the lookup's numbers pass their test (hok); that F is later than F0 (h0) and that F's arrays
have its size (hF). That all can hold together: no example is known. Nothing on soundness, on
completeness or on any other property.

The hypothesis `LookThree` (W/Join.lean: the lookup's own claim on its leaves and its two claims on
its planes are worth 0) at the world of a ledger with the entries entryTrue, from the lookup's own
sentence K3Planes (Johnson/Top/H/K3RowOut.lean). First: the three tables on the planes' matrix obey
the lookup's law of the reads, at every plan at which K4Ground holds. The library has that at its
full-size structure Rows.Pub34 (`planeTabs_pub`, `readsLaw_pub`, Johnson/Road/K4/ReadsLawPub.lean);
these two proofs read four hypotheses of that structure alone, which K4Ground has (funs, tab,
tables, NM): THE FIRST TWO PROOFS HERE ARE THE LIBRARY's, WITH THE LETTERS TURNED.

  `planeTabs_ground`   the three tables of the planes are among the tables, at the first entries
      that the environment finds under their names, with the weights that the lookup's law names.
  `readsLaw_ground`   Fo.ReadsLaw at these first entries, where every table holds what it says of M.
  `planes_true`   K4ReadsTrue (Johnson/Top/H/K4PlanesWorth.lean) at what a hearing returned, at
      every ledger, with the entries entryTrue.
  `look_of_planes`   LookThree in the world of the ledger that the run "front" leaves, by the
      library's `k4_front_K3Planes` (Johnson/Meaning/PlanesPaidK4.lean), read from right to left.
  `look_item`   the same as the field look of ItemSlots (W/ItemOfKept.lean) asks it, at a mask row
      that is ν's.
No property is claimed.
-/
import Johnson.Road.K4.W.Join
import Johnson.Road.K4.PlanesTrue
import Johnson.Meaning.PlanesPaidK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W

section Law
open Finset OnBytes.Model OnBytes.Model.Layer _root_.Fo Cb.Fo
open Inst.Model.FFSeg (Dim)

variable {K : Type} [Field K] {h : Layer.Shape} {pc : List (List String)} {v : Layer.Env}
  {rd : Layer.Reads} {r : List Layer.TableAt × List (Layer.TableAsk × List (ℕ × ℕ)) × ℕ}
  {tl : HTailF2} {H : Layer.Heard} {hd : Level} {hd2 : Option Level}
  {pts : List (String × Array E)} {funs : Array HFun} {D : Dim}

/-- **The three tables of the planes**, under the public facts on the layout. CONDITIONAL: on G, h1,
h2, h4. -/
theorem planeTabs_ground (G : K4Ground h pc v rd r tl H hd hd2 pts funs D) (ρ : Reading K)
    (mats : Array TMat) (cellM : ℕ → ℕ → ℕ → K) (ν : Pl → K)
    (h1 : (mats.getD (matIx v.y).iB {}).m / 2 ^ v.y.h.lmb = 1)
    (h2 : planeCols H.fo.shape v.y.h.lmb ≤ (mats.getD (matIx v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ v.y.h.lmb, ∀ c < planeCols H.fo.shape v.y.h.lmb,
      cellM (matIx v.y).iB r c = ν (.cell r c)) :
    ∃ tB0 tB1 tP f0 f1 fP, v.tabAt "b-bits-0" = some tB0 ∧
      v.tabAt "b-bits-1" = some tB1 ∧ v.tabAt "b-pin" = some tP ∧
      PlaneTab ρ mats funs cellM f0 tB0
        (fun r => (phiBK H.fo.shape v.y.h.lmb (rdL ρ H.fo.zb0)).getD r 0)
        H.fo.shape v.y.h.lmb ν ∧
      PlaneTab ρ mats funs cellM f1 tB1
        (fun r => (phiBK H.fo.shape v.y.h.lmb (rdL ρ H.fo.zb1)).getD r 0)
        H.fo.shape v.y.h.lmb ν ∧
      PlaneTab ρ mats funs cellM fP tP (fun r => (2 : K) ^ (r % 32)) H.fo.shape
        v.y.h.lmb ν := by
  have hf := G.funs
  have hl : layTables (matsR v.y v.g) (preAsks v.y rd v.g ++
      [planeAsk v.y "b-bits-0", planeAsk v.y "b-bits-1", planeAsk v.y "b-pin"]) 0 =
      some (v.tab, r.2.1, r.2.2) := by
    rw [G.tab, ← tableAsks_eq]
    exact G.tables
  have hl1 : layTables (matsR v.y v.g)
      ((preAsks v.y rd v.g ++ [planeAsk v.y "b-bits-0"]) ++
        planeAsk v.y "b-bits-1" :: [planeAsk v.y "b-pin"]) 0 =
      some (v.tab, r.2.1, r.2.2) := by
    rw [List.append_assoc]
    exact hl
  have hl2 : layTables (matsR v.y v.g)
      ((preAsks v.y rd v.g ++
        [planeAsk v.y "b-bits-0", planeAsk v.y "b-bits-1"]) ++
        planeAsk v.y "b-pin" :: []) 0 = some (v.tab, r.2.1, r.2.2) := by
    rw [List.append_assoc]
    exact hl
  have n0 : ∀ b ∈ preAsks v.y rd v.g, b.name ≠ "b-bits-0" :=
    fun b hb => ask_ne hb "b-bits-0" (by decide)
  have n1 : ∀ b ∈ preAsks v.y rd v.g ++ [planeAsk v.y "b-bits-0"],
      b.name ≠ "b-bits-1" := fun b hb => by
    rcases List.mem_append.mp hb with hb | hb
    · exact ask_ne hb "b-bits-1" (by decide)
    · rw [List.mem_singleton.mp hb]
      show "b-bits-0" ≠ "b-bits-1"
      decide
  have n2 : ∀ b ∈ preAsks v.y rd v.g ++
      [planeAsk v.y "b-bits-0", planeAsk v.y "b-bits-1"], b.name ≠ "b-pin" :=
    fun b hb => by
    rcases List.mem_append.mp hb with hb | hb
    · exact ask_ne hb "b-pin" (by decide)
    · rcases List.mem_cons.mp hb with rfl | hb
      · show "b-bits-0" ≠ "b-pin"
        decide
      · rw [List.mem_singleton.mp hb]
        show "b-bits-1" ≠ "b-pin"
        decide
  obtain ⟨_, _, q0⟩ := lay_find _ (planeAsk v.y "b-bits-0") rfl _ _ 0 _ _ _ n0 hl
  obtain ⟨b0, z0, _⟩ := funs_mem _ _ _ _ _ hf _ _ _ q0
  obtain ⟨_, _, q1⟩ := lay_find _ (planeAsk v.y "b-bits-1") rfl _ _ 0 _ _ _ n1 hl1
  obtain ⟨b1, z1, _⟩ := funs_mem _ _ _ _ _ hf _ _ _ q1
  have y0 : Forest.phiB H.fo v.y.h.lmb 0 = some b0 := z0
  have y1 : Forest.phiB H.fo v.y.h.lmb 1 = some b1 := z1
  obtain ⟨tB0, f0, a0, T0⟩ := layer_planeTab ρ "b-bits-0" hl n0 hf b0 z0 mats cellM
    (fun r => (phiBK H.fo.shape v.y.h.lmb (rdL ρ H.fo.zb0)).getD r 0) H.fo.shape ν
    h1 h2 (fun j _ => by
      rw [rdL_getD, phiB_val ρ H.fo v.y.h.lmb 0 b0 y0]
      rfl) h4
  obtain ⟨tB1, f1, a1, T1⟩ := layer_planeTab ρ "b-bits-1" hl1 n1 hf b1 z1 mats cellM
    (fun r => (phiBK H.fo.shape v.y.h.lmb (rdL ρ H.fo.zb1)).getD r 0) H.fo.shape ν
    h1 h2 (fun j _ => by
      rw [rdL_getD, phiB_val ρ H.fo v.y.h.lmb 1 b1 y1]
      rfl) h4
  obtain ⟨tP, fP, a2, TP⟩ := layer_planeTab ρ "b-pin" hl2 n2 hf
    (Forest.phiP v.y.h.lmb) rfl mats cellM _ H.fo.shape ν h1 h2
    (fun j hj => phiP_val ρ v.y.h.lmb j hj) h4
  exact ⟨tB0, tB1, tP, f0, f1, fP, a0, a1, a2, T0, T1, TP⟩

/-- **The lookup's law of the reads at the planes' three tables**, where every table holds what it
says of M. CONDITIONAL: on G, hRd, h1, h2, h4; and on t0, t1, t2 (the environment finds the three
tables' first entries). -/
theorem readsLaw_ground (G : K4Ground h pc v rd r tl H hd hd2 pts funs D) (ρ : Reading K)
    (W : World K) (M : Mats K) (hRd : ∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 M Fn) (ν : Pl → K)
    (h1 : (tl.mats.getD (matIx v.y).iB {}).m / 2 ^ v.y.h.lmb = 1)
    (h2 : planeCols H.fo.shape v.y.h.lmb ≤ (tl.mats.getD (matIx v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ v.y.h.lmb, ∀ c < planeCols H.fo.shape v.y.h.lmb,
      M (matIx v.y).iB r c = ν (.cell r c))
    {tB0 tB1 tP : ℕ} (t0 : v.tabAt "b-bits-0" = some tB0)
    (t1 : v.tabAt "b-bits-1" = some tB1) (t2 : v.tabAt "b-pin" = some tP) :
    ReadsLaw H.fo.shape v.y.h.lmb (rdL ρ H.fo.zb0) (rdL ρ H.fo.zb1) ν W.entry
      v.iU3 v.K3 tB0 tB1 tP := by
  obtain ⟨tB0', tB1', tP', f0, f1, fP, a0, a1, a2, T0, T1, TP⟩ :=
    planeTabs_ground G ρ tl.mats M ν h1 h2 h4
  obtain rfl : tB0' = tB0 := Option.some.inj (a0.symm.trans t0)
  obtain rfl : tB1' = tB1 := Option.some.inj (a1.symm.trans t1)
  obtain rfl : tP' = tP := Option.some.inj (a2.symm.trans t2)
  exact readsLaw_of_readsAll ρ (readsAll_of_holds ρ G.NM hRd) T0 T1 TP

end Law

section Item
open Cb Cb.Fo Cb.Fo.NumsEq TwV
open OnBytes OnBytes.Model Fo
open OnBytes.Model.Layer (Pub Own matIx)
open OnBytes.Desc.First.K4 (planesParts)
open Inst.Model.FFSeg (Dim)
open VerifiableInference.OnPublicFiles (K4ReadsTrue K3Planes planesParts_tabs)
open Meaning.Planes (readsTrue_iff_hostPlanes k4_front_K3Planes planesParts_planesL)

variable {h : Layer.Shape} {pc : List (List String)} {rd : Layer.Reads}
  {r : List Layer.TableAt × List (Layer.TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {o : Own}
  {pts : List (String × Array E)} {D : Dim}

/-- **THE THREE TRUE READS AT THE ITEM's ENTRIES**, at every ledger F and every plan. CONDITIONAL:
on G, h1, h2, h4 and that the lookup's three forms are there. -/
theorem planes_true (G : K4Ground h pc o.v rd r tl o.H o.hd o.hd2 pts o.funs D)
    (Mm : Mats Cb.Gl.E) (F : Fork) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (h1 : (tl.mats.getD (matIx o.v.y).iB {}).m / 2 ^ o.v.y.h.lmb = 1)
    (h2 : planeCols o.H.fo.shape o.v.y.h.lmb ≤ (tl.mats.getD (matIx o.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      Mm (matIx o.v.y).iB r c = ν (.cell r c))
    {pp : Aff × List Aff} (hpp : planesParts o.v o.H.fo = some pp) :
    K4ReadsTrue Reading.gl o.v o.H.fo F ν (entryTrue tl o Mm) :=
  k4ReadsTrue_of_law Reading.gl hpp F ν _ fun _ _ _ t0 t1 tp =>
    readsLaw_ground G Reading.gl (F.worldOf Reading.gl (fun j => ν (.mask j)) (entryTrue tl o Mm))
      Mm (holds_item G Mm F _) ν h1 h2 h4 t0 t1 tp

/-- **LookThree FROM THE LOOKUP's OWN SENTENCE ON ITS PLANES.** F0: a ledger at which the rounds rs
are what the lookup has heard. CONDITIONAL: on every hypothesis named. -/
theorem look_of_planes {rows : Bool} {P : Pub} {g : ℕ} {F G : Fork} {fs : Array Aff}
    (hfr : Desc.First.K4.formsFrontWith rows P g o F = some (fs, G))
    (Gr : K4Ground h pc o.v rd r tl o.H o.hd o.hd2 pts o.funs D) (Mm : Mats Cb.Gl.E)
    {F0 : Fork} {first : ℕ} {rs : TwV.Rounds Cb.Gl.E}
    (hI : _root_.Fo.HeardIs Reading.gl o.H.fo F0
      (_root_.Fo.endsOf o.H.fo.shape o.v.y.h.lmb first rs))
    (h0 : _root_.Fo.Later F0 F) (hok : FoNums.ok o.H.fo.shape = true) (hF : PscRun.Sized F)
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (h1 : (tl.mats.getD (matIx o.v.y).iB {}).m / 2 ^ o.v.y.h.lmb = 1)
    (h2 : planeCols o.H.fo.shape o.v.y.h.lmb ≤ (tl.mats.getD (matIx o.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      Mm (matIx o.v.y).iB r c = ν (.cell r c))
    (hP : K3Planes o.H.fo.shape o.v.y.h.lmb first ν rs)
    {pp : Aff × List Aff} (hpp : planesParts o.v o.H.fo = some pp) :
    LookThree Reading.gl (G.worldOf Reading.gl (fun j => ν (.mask j)) (entryTrue tl o Mm)) o
      pp := by
  obtain ⟨tB0, tB1, tP, b0, b1, b2⟩ := planesParts_tabs hpp
  have hK := (readsTrue_iff_hostPlanes Reading.gl b0 b1 b2).1
    (planes_true Gr Mm G ν h1 h2 h4 hpp)
  have z := (k4_front_K3Planes Reading.gl hfr hI h0 hok hF (_root_.Fo.Later.refl G) ν _ b0 b1 b2
    hK).2 hP _ (planesParts_planesL hpp)
  exact ⟨z _ List.mem_cons_self, fun f hf => z f (List.mem_cons_of_mem _ hf)⟩

/-- **The field look of ItemSlots**, at a mask row that is ν's. CONDITIONAL: as look_of_planes, and
on hm. -/
theorem look_item {rows : Bool} {P : Pub} {g : ℕ} {F G : Fork} {fs : Array Aff}
    (hfr : Desc.First.K4.formsFrontWith rows P g o F = some (fs, G))
    (Gr : K4Ground h pc o.v rd r tl o.H o.hd o.hd2 pts o.funs D) (Mm : Mats Cb.Gl.E)
    {F0 : Fork} {first : ℕ} {rs : TwV.Rounds Cb.Gl.E}
    (hI : _root_.Fo.HeardIs Reading.gl o.H.fo F0
      (_root_.Fo.endsOf o.H.fo.shape o.v.y.h.lmb first rs))
    (h0 : _root_.Fo.Later F0 F) (hok : FoNums.ok o.H.fo.shape = true) (hF : PscRun.Sized F)
    (ν : _root_.Fo.Pl → Cb.Gl.E) {mask : ℕ → Cb.Gl.E} (hm : mask = fun j => ν (.mask j))
    (h1 : (tl.mats.getD (matIx o.v.y).iB {}).m / 2 ^ o.v.y.h.lmb = 1)
    (h2 : planeCols o.H.fo.shape o.v.y.h.lmb ≤ (tl.mats.getD (matIx o.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      Mm (matIx o.v.y).iB r c = ν (.cell r c))
    (hP : K3Planes o.H.fo.shape o.v.y.h.lmb first ν rs) :
    ∀ pp, planesParts o.v o.H.fo = some pp →
      LookThree Reading.gl (G.worldOf Reading.gl mask (entryTrue tl o Mm)) o pp := by
  intro pp hpp
  rw [hm]
  exact look_of_planes hfr Gr Mm hI h0 hok hF ν h1 h2 h4 hP hpp

end Item

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.planeTabs_ground
#print axioms OnBytes.Road.K4.W.readsLaw_ground
#print axioms OnBytes.Road.K4.W.planes_true
#print axioms OnBytes.Road.K4.W.look_of_planes
#print axioms OnBytes.Road.K4.W.look_item
