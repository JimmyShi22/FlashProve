-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ReadsAtPub.lean: ReadsTrue at EVERY public record Pub34 that is tied to a hearing of
K4's text by PubAt (Johnson/Road/K4/PubAt.lean), in the world of every ledger and every mask row
with the entries entryTrue tl o M (Johnson/Road/K4/EntryTrue.lean), for any smallness test's
numbers tl with the plan's matrices.

PubAt names neither the record's list of tables nor its smallness test's numbers. Both are fixed all
the same, as far as ReadsTrue reads them:
  the list of tables is made by the record's own lines (hrd, hl, hpts, hfun) from its environment
  and from what was heard, which PubAt ties to the hearing's return o; and the hearing has made
  o.funs by the same calls (hear_public, OnBytes/Desc/First/K4/HearPublic.lean);
  of the smallness test's numbers ReadsTrue reads the function tabAt alone, which reads the number
  of matrices and each matrix's rows and columns alone.

Main names:
  `tabAt_congr`: two records of numbers with the same rows and columns, each with NM its number of
    matrices, have one function tabAt.
  `holds_entryOf_at`: holds_entryOf at another record of numbers with the same tabAt.
  `funs_of_pubAt`: X.funs = o.funs.
  `reads_of_pubAt`: ReadsTrue.
Limits. TRUE BY MAKE, as EntryTrue.lean says: the entries are chosen so. Premises: PubAt; the
hearing's return; two public lines of the plan (hrd, hmats: fields of PubLines); that tl has the
plan's matrices (htm, hNM: fields of PubLines too). By the head of
Johnson/Road/Rows/LayerEnds34.lean no record Pub34 exists at the small example: there the statements
are empty. Nothing ties these entries to what a prover has committed. Nothing on a draw, on
soundness or on hiding.


-/
import Johnson.Road.K4.EntryTrue
import Johnson.Road.K4.PubAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Heard Pub Own readsOf HPlan2 layTables tableAsks)
open OnBytes.Desc.First.K4 (engFl hear)
open OnBytes.Desc.First.P1 (gl)
open Inst.Model (Tables)
open Inst.Model.FFSeg (Dim)

/-- Rows and columns of member i, off the list of pairs. -/
theorem pair_getD (a : Array TMat) (i : ℕ) :
    (a.map fun M => (M.m, M.k)).getD i (0, 0) = ((a.getD i {}).m, (a.getD i {}).k) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[i]? <;> rfl

/-- The function tabAt reads the number of matrices and their rows and columns alone. -/
theorem tabAt_congr {tl tl' : HTailF2}
    (hm : (tl.mats.map fun M => (M.m, M.k)) = tl'.mats.map fun M => (M.m, M.k))
    (hN : tl.NM = tl.mats.size) (hN' : tl'.NM = tl'.mats.size) (Fn : HFun) (c sg : ℕ) :
    tl.tabAt Fn c sg = tl'.tabAt Fn c sg := by
  have hs : tl.mats.size = tl'.mats.size := by
    have e := congrArg Array.size hm
    rwa [Array.size_map, Array.size_map] at e
  have hp : ((tl.mats.getD Fn.mat {}).m, (tl.mats.getD Fn.mat {}).k) =
      ((tl'.mats.getD Fn.mat {}).m, (tl'.mats.getD Fn.mat {}).k) := by
    rw [← pair_getD, ← pair_getD, hm]
  have e1 : (tl.mats.getD Fn.mat {}).m = (tl'.mats.getD Fn.mat {}).m := congrArg Prod.fst hp
  have e2 : (tl.mats.getD Fn.mat {}).k = (tl'.mats.getD Fn.mat {}).k := congrArg Prod.snd hp
  unfold HTailF2.tabAt
  simp only [hN, hN', hs, e1, e2]

variable {K : Type} [Field K]

/-- In every world with the entries of tl, every table holds what it says at tl' too. -/
theorem holds_entryOf_at (ρ : Reading K) {tl tl' : HTailF2} {funs : Array HFun}
    (hA : Apart tl funs) (hT : ∀ Fn c sg, tl'.tabAt Fn c sg = tl.tabAt Fn c sg) (iU3 K3 : ℕ)
    (M : Mats K) {W : World K} (hW : W.entry = entryOf ρ tl funs iU3 K3 M) :
    ∀ Fn ∈ funs, Holds ρ W tl' iU3 K3 M Fn := by
  intro Fn hF c sg pos hpos
  rw [hT] at hpos
  exact holds_entryOf ρ hA iU3 K3 M hW Fn hF c sg pos hpos

/-- **The record's list of tables is the hearing's.** -/
theorem funs_of_pubAt {X : Rows.Pub34 Cb.Gl.E} {Pp : Pub} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {o : Own} {F G G2 : Fork} {t0 u t4 : Tape} {D : Dim} {tb : Tables}
    {hS : Layer.Shape} (PX : PubAt X Pp hp fo o G2 t4 D tb hS)
    (h : hear engFl Pp hp g fo F t0 = some (o, G, u)) (hrd : readsOf Pp.y = .ok Pp.rd)
    (hmats : ((Pp.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR Pp.y g) :
    X.funs = o.funs := by
  obtain ⟨_, _, iU3, tab, laid, nU3, TS, claimsP, pts, hd2, _, _, e5, _, ev, _, _, ehd2, e9,
    e10⟩ := Desc.First.K4.hear_public h
  have vy : o.v.y = Pp.y := by rw [ev]
  have vg : o.v.g = g := by rw [ev]
  have xrd : Pp.rd = X.rd := by
    have a := X.hrd
    rw [PX.v, vy, hrd] at a
    exact Except.ok.inj a
  have xl : (tab, laid, nU3) = X.r := by
    have a := X.hl
    rw [PX.v, vy, vg, ← xrd, ← hmats, e5] at a
    exact Option.some.inj a
  have xp : pts = X.pts := by
    have a := X.hpts
    rw [PX.v, vy, PX.H, PX.hd, PX.hd2, ehd2, e9] at a
    exact Option.some.inj a
  have a := X.hfun
  rw [PX.v, vy, PX.H, PX.fo, ← xp, ← xl, e10] at a
  exact (Option.some.inj a).symm

/-- **ReadsTrue at every record that is tied to the hearing.** -/
theorem reads_of_pubAt {X : Rows.Pub34 Cb.Gl.E} {Pp : Pub} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {o : Own} {F G G2 : Fork} {t0 u t4 : Tape} {D : Dim} {tb : Tables}
    {hS : Layer.Shape} (PX : PubAt X Pp hp fo o G2 t4 D tb hS)
    (h : hear engFl Pp hp g fo F t0 = some (o, G, u)) (hrd : readsOf Pp.y = .ok Pp.rd)
    (hmats : ((Pp.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR Pp.y g)
    {tl : HTailF2} (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR Pp.y g)
    (hNM : tl.NM = tl.mats.size) (M : Mats Cb.Gl.E) (Fl : Fork) (mask : ℕ → Cb.Gl.E) :
    X.ReadsTrue (Fl.worldOf gl mask (entryTrue tl o M)) M := by
  have ef := funs_of_pubAt PX h hrd hmats
  obtain ⟨_, _, iU3, tab, laid, nU3, TS, claimsP, pts, hd2, _, _, e5, _, ev, _, _, _, _,
    e10⟩ := Desc.First.K4.hear_public h
  have vy : o.v.y = Pp.y := by rw [ev]
  have vg : o.v.g = g := by rw [ev]
  have hT : ∀ Fn c sg, X.tl.tabAt Fn c sg = tl.tabAt Fn c sg :=
    tabAt_congr (by rw [X.htm, PX.v, vy, vg, htm]) X.hNM hNM
  have hl : layTables (tl.mats.map fun M => (M.m, M.k)) (tableAsks Pp.y Pp.rd g) 0 =
      some (tab, laid, nU3) := by
    rw [htm, ← hmats]
    exact e5
  have hA : Apart tl o.funs := apart_of_run hl e10 hNM
  intro Fn hF
  rw [ef] at hF
  rw [PX.ρ, PX.v]
  exact holds_entryOf_at gl hA hT o.v.iU3 o.v.K3 M rfl Fn hF

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tabAt_congr
#print axioms OnBytes.Road.K4.funs_of_pubAt
#print axioms OnBytes.Road.K4.reads_of_pubAt
