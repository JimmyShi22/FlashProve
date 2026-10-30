-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PlanesAtPub.lean: the three true reads of the planes' tables (K4ReadsTrue,
Johnson/Top/H/K4PlanesWorth.lean) at a hearing of K4's text, in the letters of the hearing's return
o, in the world of every ledger, with the entries entryTrue tl o M
(Johnson/Road/K4/EntryTrue.lean).

It lays k4ReadsTrue_pub (Johnson/Road/K4/PlanesTrue.lean) at a public record that is tied to the
hearing by PubAt, with ReadsTrue paid by reads_of_pubAt (Johnson/Road/K4/ReadsAtPub.lean). The
record stands in no conclusion.

  `k4ReadsTrue_of_pubAt`: K4ReadsTrue gl o.v o.H.fo H nu (entryTrue tl o M), where planesParts has
    returned.
  `k4ReadsTrue_of_front`: the same where K4's first run of claims formsFrontWith has returned (the
    return of planesParts by front_cut, Johnson/Top/H/K4PlanesWorth.lean).
Limits. TRUE BY MAKE, as EntryTrue.lean says. Premises: a record with PubAt; the hearing's return;
four public lines of the plan (hrd, hmats, htm, hNM: fields of PubLines); that the planes' matrix in
tl has its rows in one run of 2 ^ lmb (h1) and at least the planes' columns (h2); that the planes'
cells under nu are the entries of the planes' matrix in M (h4). Nothing ties the entries to what a
prover has committed. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.PlanesTrue
import Johnson.Road.K4.ReadsAtPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.K.Kc Cb.Fo
open _root_.Fo hiding gl
open OnBytes.Model.Layer (Heard Pub Own readsOf HPlan2 matIx)
open OnBytes.Desc.First.K4 (engFl hear planesParts formsFrontWith)
open OnBytes.Desc.First.P1 (gl)
open Inst.Model (Tables)
open Inst.Model.FFSeg (Dim)
open VerifiableInference.OnPublicFiles (K4ReadsTrue front_cut)

/-- **The three true reads at a hearing, where planesParts has returned.** -/
theorem k4ReadsTrue_of_pubAt {X : Rows.Pub34 Cb.Gl.E} {Pp : Pub} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {o : Own} {F G G2 : Fork} {t0 u t4 : Tape} {D : Dim} {tb : Tables}
    {hS : Layer.Shape} (PX : PubAt X Pp hp fo o G2 t4 D tb hS)
    (h : hear engFl Pp hp g fo F t0 = some (o, G, u)) (hrd : readsOf Pp.y = .ok Pp.rd)
    (hmats : ((Pp.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR Pp.y g)
    {tl : HTailF2} (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR Pp.y g)
    (hNM : tl.NM = tl.mats.size) (M : Mats Cb.Gl.E) (H : Fork) (ν : Pl → Cb.Gl.E)
    (h1 : (tl.mats.getD (matIx o.v.y).iB {}).m / 2 ^ o.v.y.h.lmb = 1)
    (h2 : planeCols o.H.fo.shape o.v.y.h.lmb ≤ (tl.mats.getD (matIx o.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      M (matIx o.v.y).iB r c = ν (.cell r c))
    {pp : Aff × List Aff} (hpp : planesParts o.v o.H.fo = some pp) :
    K4ReadsTrue gl o.v o.H.fo H ν (entryTrue tl o M) := by
  obtain ⟨_, _, iU3, tab, laid, nU3, TS, claimsP, pts, hd2, _, _, _, _, ev, _, _, _, _, _⟩ :=
    Desc.First.K4.hear_public h
  have vy : o.v.y = Pp.y := by rw [ev]
  have vg : o.v.g = g := by rw [ev]
  have hq : ∀ i, ((X.tl.mats.getD i {}).m, (X.tl.mats.getD i {}).k) =
      ((tl.mats.getD i {}).m, (tl.mats.getD i {}).k) := fun i => by
    rw [← pair_getD, ← pair_getD, X.htm, PX.v, vy, vg, htm]
  have e1 : ∀ i, (X.tl.mats.getD i {}).m = (tl.mats.getD i {}).m := fun i =>
    congrArg Prod.fst (hq i)
  have e2 : ∀ i, (X.tl.mats.getD i {}).k = (tl.mats.getD i {}).k := fun i =>
    congrArg Prod.snd (hq i)
  have R := reads_of_pubAt PX h hrd hmats htm hNM M H (fun j => ν (.mask j))
  have key := k4ReadsTrue_pub X M H ν (entryTrue tl o M) (by rw [PX.ρ]; exact R)
    (by rw [PX.v, e1]; exact h1)
    (by rw [PX.v, PX.H, e2]; exact h2)
    (by rw [PX.v, PX.H]; exact h4) (pp := pp) (by rw [PX.v, PX.H]; exact hpp)
  rw [PX.ρ, PX.v, PX.H] at key
  exact key

/-- **The same where K4's first run of claims has returned.** -/
theorem k4ReadsTrue_of_front {X : Rows.Pub34 Cb.Gl.E} {Pp : Pub} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {o : Own} {F G G2 : Fork} {t0 u t4 : Tape} {D : Dim} {tb : Tables}
    {hS : Layer.Shape} (PX : PubAt X Pp hp fo o G2 t4 D tb hS)
    (h : hear engFl Pp hp g fo F t0 = some (o, G, u)) (hrd : readsOf Pp.y = .ok Pp.rd)
    (hmats : ((Pp.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR Pp.y g)
    {tl : HTailF2} (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR Pp.y g)
    (hNM : tl.NM = tl.mats.size) (M : Mats Cb.Gl.E) (H : Fork) (ν : Pl → Cb.Gl.E)
    (h1 : (tl.mats.getD (matIx o.v.y).iB {}).m / 2 ^ o.v.y.h.lmb = 1)
    (h2 : planeCols o.H.fo.shape o.v.y.h.lmb ≤ (tl.mats.getD (matIx o.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      M (matIx o.v.y).iB r c = ν (.cell r c))
    {rows : Bool} {P' : Pub} {g' : ℕ} {F0 G0 : Fork} {fs : Array Aff}
    (hf : formsFrontWith rows P' g' o F0 = some (fs, G0)) :
    K4ReadsTrue gl o.v o.H.fo H ν (entryTrue tl o M) := by
  obtain ⟨_, _, pp, _, _, a3, _⟩ := front_cut hf
  exact k4ReadsTrue_of_pubAt PX h hrd hmats htm hNM M H ν h1 h2 h4 a3

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4ReadsTrue_of_pubAt
#print axioms OnBytes.Road.K4.k4ReadsTrue_of_front
