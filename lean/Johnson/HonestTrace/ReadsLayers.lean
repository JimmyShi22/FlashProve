-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/ReadsLayers.lean

The vector of reads of an honest prover in the sub-proof of a group of layers, at the list of tables
that the verifier of OnBytes/Model/ makes; at a run of the layers' plain hearing it meets the law of
the reads, in three wordings, and the lookup's law at the three tables of the planes.

The verifier of OnBytes/Model/ makes the list of a group's tables in two steps. "Layer.layTables"
lays the families of tables one behind the other, from public numbers alone. "Layer.funsOf"
(OnBytes/Model/Layer.lean) gives each laid table its weights, from what the lookup left (fo) and
from a list of named points (pt, which "Layer.pointsOf" makes of what was heard). The description's
hearing of a group's own rounds calls the same functions (OnBytes/Desc/First/K4/Hear.lean). Here no
list is written anew: "layerParts" is the answer of "funsOf", and an entry of the vector is "readAt"
(Johnson/Desc/K8/Honest/Arrays.lean) at that list.

Which list of matrices. The hearing lays the tables by the sizes of the group's own list,
(P.tails.getD g {}).mats. The plan's numbers of the smallness test hold another list, hp.tl.mats,
which differs from it in fields of the borrowed matrices and, where "Layer.planG" returns hp, has
the same rows and columns ("sameSizes_plan"). The theorems at a run therefore stand at every list
mats with the sizes of the group's own ("SameSizes", Johnson/HonestTrace/Reads.lean).

Main definitions:
* "layerParts y fo pt laid": the list that "funsOf" returns; empty where it returns nothing: there
  the vector is 0 at every number, and no theorem of this file speaks.
* "u3Layers mats y fo pt laid cell i": entry i of the vector, at the sizes of mats and the integers
  cell.
Main theorems (hh: a run of the layers' plain hearing "hearFl P hp g fo" returns o):
* "tablesLie_layers", "readsAll_layers": wherever "layTables" and "funsOf" return.
* "sameSizes_plan": the list in a plan that "Layer.planG" returns has the sizes of the group's own.
* "layerParts_hear": under hh, at what "layTables" returns for the group's asks and what "pointsOf"
  returns at o's heard values, "layerParts" is the list o.funs that the run leaves.
  "sentReads_hear": so a table of entries that holds "u3Layers" at these meets "SentReads" at
  o.funs. "hear_names": under hh the two functions return.
* "tablesLie_hear", "readsAll_hear", "holds_hear", "tieThird_hear": under hh, at the plan's number
  of reads: "TablesLie"; at the run's own array and width "Fo.ReadsAll", and every table holds what
  it says ("Holds", Johnson/Road/FormsKeysMat.lean); at row 0 of any array the third clause of the
  smallness test's tie ("TieThird", Johnson/Desc/Kinds/Law/TieReads.lean).
* "readsLaw_hear": "Fo.ReadsLaw" at the three tables on the planes' matrix b, at the lookup's two
  heard points read by ρ; by "k4_readsLaw" (Johnson/Meaning/PlanesHost.lean).

Limits. fo, and what the run hears, are letters: how they come from an honest run's challenges is
not said here. That the functions return, and hh, are premises. The premise on the table of entries
is as in Johnson/HonestTrace/Reads.lean: nothing here sends a vector. "readsLaw_hear" has the three
premises of "k4_readsLaw" on the planes' matrix: its rows are one stretch of 2 ^ lmb, it has at
least the planes' columns, and ν reads its cells. The first two are shown at the group's own list
by "k4_numbers" (Johnson/Meaning/PlanesNumbers.lean), under three further premises (the planes'
forms are there; the lists are those of the layout; g is a group's number), and, where "publicOf"
returns the public part and the heard lookup has the layout's shape, at a plan's list by
"public_planeMatB" (OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPubG.lean).

Ground. This file imports Johnson/Desc/K8/Honest/Arrays.lean, through
Johnson/HonestTrace/Reads.lean: it can be built only where the files under Johnson/Desc/K8/Honest/
lie.

Not claimed: that a verifier accepts a proof made of these entries (completeness of the protocol);
anything on soundness or on what a proof shows of the cells.
-/
import Johnson.HonestTrace.ReadsTie
import Johnson.Meaning.PlanesLaid
import OnBytes.Desc.First.K4.HearPublic
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPubG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.K8 (Par)
open VerifiableInference.Desc.First.K8.Honest (CellsAt)
open OnBytes.Model.Layer (Lay TableAsk TableAt layTables funsOf pointsOf tableAsks Pub Own HPlan2
  matIx)
open OnBytes.K.Kc
open OnBytes.Desc.First.K4 (hearFl hear_public)
open Meaning.Planes (laid_public k4_tables_apart k4_readsLaw)

local notation "readAtP" => VerifiableInference.Desc.First.K8.Honest.readAt

/-! ## The list and the vector -/

/-- **The list of tables of a group of layers**: what "funsOf" of OnBytes/Model/ returns at the
layout y, the lookup's heard values fo, the named points pt and what "layTables" has laid; empty
where "funsOf" returns nothing. -/
def layerParts (y : Lay) (fo : Forest.Heard) (pt : List (String × Array E))
    (laid : List (TableAsk × List (ℕ × ℕ))) : List HFun := ((funsOf y fo pt laid).getD #[]).toList

/-- **Entry i of the vector of reads of a group of layers**, at the sizes of mats and the integers
cell. -/
def u3Layers (mats : Array TMat) (y : Lay) (fo : Forest.Heard) (pt : List (String × Array E))
    (laid : List (TableAsk × List (ℕ × ℕ))) (cell : CellsAt) (i : ℕ) : E :=
  readAtP (parOfMats mats) (layerParts y fo pt laid) cell i

/-- Where "funsOf" returns funs, the list is funs. -/
theorem layerParts_some {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)}
    {laid : List (TableAsk × List (ℕ × ℕ))} {funs : Array HFun}
    (hf : funsOf y fo pt laid = some funs) : layerParts y fo pt laid = funs.toList := by
  unfold layerParts
  rw [hf]
  rfl

/-- What "layTables" and "funsOf" make ends at or below the number of entries that "layTables"
returns, and no entry lies in two tables. -/
theorem tablesLie_layers {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)}
    {mats : Array TMat} {asks : List TableAsk} {tab : List TableAt}
    {laid : List (TableAsk × List (ℕ × ℕ))} {n : ℕ} {funs : Array HFun}
    (hl : layTables (mats.map fun M => (M.m, M.k)) asks 0 = some (tab, laid, n))
    (hf : funsOf y fo pt laid = some funs) : TablesLie mats funs n :=
  ⟨(laid_public hl hf).1, (laid_public hl hf).2⟩

/-- **The list of matrices in a plan that "planG" returns has the rows and columns of the group's
own list.** -/
theorem sameSizes_plan {P : Pub} {g : ℕ} {O : Option HPlan2} {hp : HPlan2}
    (h : Layer.planG P g O = .ok hp) : SameSizes (P.tails.getD g {}).mats hp.tl.mats := by
  obtain ⟨r, hb, hm⟩ := _root_.Fo.PlaneMatG.planG_mats P g O hp h
  rw [hm]
  have q := _root_.Fo.PlaneMatG.sameMK_getD (_root_.Fo.PlaneMatG.bordersOf_keeps hb)
  exact fun a => ⟨(q a).1.symm, (q a).2.symm⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- **The law of the reads at a group of layers.** Where "layTables" returns (tab, laid, n) at the
sizes of mats and "funsOf" returns funs, ρ reads integers as integers, and the first n entries of
array iU3 are "u3Layers" read by ρ, "Fo.ReadsAll" holds of these entries at the integers' images. -/
theorem readsAll_layers (hZ : ∀ z : ℤ, ρ.val (ofInt z) = (z : K)) {y : Lay} {fo : Forest.Heard}
    {pt : List (String × Array E)} {mats : Array TMat} {asks : List TableAsk}
    {tab : List TableAt} {laid : List (TableAsk × List (ℕ × ℕ))} {n : ℕ} {funs : Array HFun}
    (hl : layTables (mats.map fun M => (M.m, M.k)) asks 0 = some (tab, laid, n))
    (hf : funsOf y fo pt laid = some funs) {cell : CellsAt} {entry : ℕ → ℕ → ℕ → K} {iU3 K3 : ℕ}
    (S : ∀ i < n, _root_.Fo.u3Val entry iU3 K3 i = ρ.val (u3Layers mats y fo pt laid cell i)) :
    _root_.Fo.ReadsAll ρ mats funs entry iU3 K3 (castM cell) := by
  refine readsAll_sent ρ hZ (parFits_parOfMats mats) (tablesLie_layers hl hf) fun i hi => ?_
  rw [S i hi]
  unfold u3Layers
  rw [layerParts_some hf]

end

/-! ## At a run of the layers' plain hearing -/

section Run
variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork} {t t' : Tape} {o : Own}

/-- **The list by name, at a run.** hh: a run of the layers' plain hearing returns o. laid: what
"layTables" returns for the group's asks at the sizes of the group's own list; pt: what "pointsOf"
returns at the values that the run has heard. Then "layerParts" is the list that the run leaves. -/
theorem layerParts_hear (hh : hearFl P hp g fo F t = some (o, F', t')) {tab : List TableAt}
    {laid : List (TableAsk × List (ℕ × ℕ))} {n : ℕ} {pt : List (String × Array E)}
    (hl : layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) (tableAsks P.y P.rd g) 0 =
      some (tab, laid, n))
    (hpt : pointsOf P.y o.H o.hd o.hd2 = some pt) :
    layerParts P.y fo pt laid = o.funs.toList := by
  obtain ⟨_, _, _, tab', laid', n', _, _, pts, hd2, _, _, hl', _, _, _, _, h2, hp', hf⟩ :=
    hear_public hh
  rw [hl] at hl'
  obtain ⟨-, rfl, -⟩ : tab = tab' ∧ laid = laid' ∧ n = n' := by
    simpa only [Option.some.injEq, Prod.mk.injEq] using hl'
  rw [h2, hp'] at hpt
  obtain rfl := Option.some.inj hpt
  exact layerParts_some hf

/-- Under hh the two functions return: there are tab, laid, n and pt as "layerParts_hear" asks. -/
theorem hear_names (hh : hearFl P hp g fo F t = some (o, F', t')) :
    ∃ tab laid n pt,
      layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) (tableAsks P.y P.rd g) 0 =
        some (tab, laid, n) ∧ pointsOf P.y o.H o.hd o.hd2 = some pt := by
  obtain ⟨_, _, _, tab, laid, n, _, _, pts, hd2, _, _, hl, _, _, _, _, h2, hp', _⟩ := hear_public hh
  exact ⟨tab, laid, n, pts, hl, by rw [h2]; exact hp'⟩

/-- The tables that a run of the layers' plain hearing leaves end at or below the plan's number of
reads, and no entry lies in two of them, at every list with the sizes of the group's own. -/
theorem tablesLie_hear (hh : hearFl P hp g fo F t = some (o, F', t')) {mats : Array TMat}
    (hm : SameSizes (P.tails.getD g {}).mats mats) : TablesLie mats o.funs (hp.nU.getD 2 0) :=
  TablesLie.same hm ⟨(k4_tables_apart hh).1, (k4_tables_apart hh).2⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- Under the premises of "layerParts_hear", a table of entries that holds "u3Layers", at the list
by name, meets "SentReads" at the list that the run leaves. -/
theorem sentReads_hear (hh : hearFl P hp g fo F t = some (o, F', t')) {tab : List TableAt}
    {laid : List (TableAsk × List (ℕ × ℕ))} {n : ℕ} {pt : List (String × Array E)}
    (hl : layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) (tableAsks P.y P.rd g) 0 =
      some (tab, laid, n))
    (hpt : pointsOf P.y o.H o.hd o.hd2 = some pt) {mats : Array TMat} {cell : CellsAt}
    {entry : ℕ → ℕ → ℕ → K} {iU3 K3 k : ℕ}
    (S : ∀ i < k, _root_.Fo.u3Val entry iU3 K3 i = ρ.val (u3Layers mats P.y fo pt laid cell i)) :
    SentReads ρ (parOfMats mats) o.funs.toList cell entry iU3 K3 k := by
  intro i hi
  rw [S i hi]
  unfold u3Layers
  rw [layerParts_hear hh hl hpt]

/-- **The law of the reads at the tables that a run of the layers' plain hearing leaves**: at every
list mats with the sizes of the group's own, the run's own array of the reads and its width, and
the plan's number of reads. p: any numbers of a place with the sizes of mats. Premises: ρ reads
integers as integers; the entries meet "SentReads" at p, these tables and the cells. -/
theorem readsAll_hear (hZ : ∀ z : ℤ, ρ.val (ofInt z) = (z : K))
    (hh : hearFl P hp g fo F t = some (o, F', t')) {mats : Array TMat}
    (hm : SameSizes (P.tails.getD g {}).mats mats) {p : Par} (Pf : ParFits p mats)
    {cell : CellsAt} {entry : ℕ → ℕ → ℕ → K}
    (S : SentReads ρ p o.funs.toList cell entry o.v.iU3 o.v.K3 (hp.nU.getD 2 0)) :
    _root_.Fo.ReadsAll ρ mats o.funs entry o.v.iU3 o.v.K3 (castM cell) :=
  readsAll_sent ρ hZ Pf (tablesLie_hear hh hm) S

/-- **The lookup's law of the reads at the three tables on the planes' matrix b**, under the
premises of "readsAll_hear", at the lookup's two heard points on the planes, read by ρ. h1: the
matrix's rows are one stretch of 2 ^ lmb; h2: it has at least the planes' columns; h4: ν reads its
cells' images. -/
theorem readsLaw_hear (hZ : ∀ z : ℤ, ρ.val (ofInt z) = (z : K))
    (hh : hearFl P hp g fo F t = some (o, F', t')) {mats : Array TMat}
    (hm : SameSizes (P.tails.getD g {}).mats mats) {p : Par} (Pf : ParFits p mats)
    {cell : CellsAt} {entry : ℕ → ℕ → ℕ → K}
    (S : SentReads ρ p o.funs.toList cell entry o.v.iU3 o.v.K3 (hp.nU.getD 2 0))
    (ν : _root_.Fo.Pl → K)
    (h1 : (mats.getD (matIx o.v.y).iB {}).m / 2 ^ o.v.y.h.lmb = 1)
    (h2 : _root_.Fo.planeCols o.H.fo.shape o.v.y.h.lmb ≤ (mats.getD (matIx o.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < _root_.Fo.planeCols o.H.fo.shape o.v.y.h.lmb,
      ((cell (matIx o.v.y).iB r c : ℤ) : K) = ν (.cell r c)) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      _root_.Fo.ReadsLaw o.H.fo.shape o.v.y.h.lmb (_root_.Fo.rdL ρ o.H.fo.zb0)
        (_root_.Fo.rdL ρ o.H.fo.zb1) ν entry o.v.iU3 o.v.K3 tB0 tB1 tP :=
  k4_readsLaw ρ hh _ _ rfl rfl mats (castM cell) ν h1 h2 h4 entry _ _
    (readsAll_hear ρ hZ hh hm Pf S)

end

/-- **Every table that a run of the layers' plain hearing leaves holds what it says of the cells'
images, in a world whose entries meet "SentReads"**, in the words of
Johnson/Road/FormsKeysMat.lean. tl: numbers of the smallness test whose list of matrices has the
sizes of the group's own; ρ reads integers as integers. -/
theorem holds_hear {K : Type} [Field K] (ρ : Reading K) (hZ : ∀ z : ℤ, ρ.val (ofInt z) = (z : K))
    (hh : hearFl P hp g fo F t = some (o, F', t')) {tl : HTailF2}
    (hm : SameSizes (P.tails.getD g {}).mats tl.mats) {p : Par} (Pf : ParFits p tl.mats)
    {cell : CellsAt} {W : World K}
    (S : SentReads ρ p o.funs.toList cell W.entry o.v.iU3 o.v.K3 (hp.nU.getD 2 0)) :
    ∀ Fn ∈ o.funs, Road.Holds ρ W tl o.v.iU3 o.v.K3 (castM cell) Fn :=
  holds_sent ρ hZ Pf (tablesLie_hear hh hm) S

/-- **The third clause of the smallness test's tie at a group of layers**: tl: numbers of the
smallness test whose list of matrices has the sizes of the group's own and whose tables are those
that the run leaves; A: a table of cells whose row 0 of the array u3 holds the vector, read, below
the plan's number of reads. -/
theorem tieThird_hear (hh : hearFl P hp g fo F t = some (o, F', t')) {tl : HTailF2}
    (hm : SameSizes (P.tails.getD g {}).mats tl.mats) (hfuns : tl.funs = o.funs) {p : Par}
    (Pf : ParFits p tl.mats) {cell : CellsAt} {u3 : ℕ} {A : ℕ → ℕ → ℕ → Cb.Gl.E}
    (S : ∀ i < hp.nU.getD 2 0, A u3 0 i = Reading.gl.val (readAtP p o.funs.toList cell i)) :
    VerifiableInference.Desc.Kinds.Head.Law.TieThird tl u3 A cell :=
  tieThird_sent Pf (by rw [hfuns]; exact tablesLie_hear hh hm) (by rw [hfuns]; exact S)

end Run

#print axioms layerParts_some
#print axioms tablesLie_layers
#print axioms sameSizes_plan
#print axioms readsAll_layers
#print axioms layerParts_hear
#print axioms hear_names
#print axioms tablesLie_hear
#print axioms sentReads_hear
#print axioms readsAll_hear
#print axioms readsLaw_hear
#print axioms holds_hear
#print axioms tieThird_hear

end OnBytes.HonestTrace
