-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseReads.lean: AT A YES OF THE PIECE THAT HOLDS K4's BLOCK, IN A GROUP THAT IS NOT
THE FIRST: THE TRUE READS, WHERE THE STATEMENT's LETTER FOR THE TRUE VALUE OF AN ENTRY IS FILLED BY
THE DEFINITION `entryTrue` (Johnson/Road/K4/EntryTrue.lean). A record and three theorems. Glue:
`reads_of_pubAt` (ReadsAtPub.lean) and `k4ReadsTrue_of_front` (PlanesAtPub.lean) laid at a `Yes`.
No draw, no count.

  `ReadsAre par Sm nu tl h3 Mt`: FOUR LINES: entry: the statement's `Sem.entryT` at o and w is
  `entryTrue tl o (Mt w)` · one: the planes' matrix has its rows in one run of 2 ^ lmb · cols: it
  has at least the planes' columns at the shape h3 · cell: the planes' cells under the valuation nu
  w are the entries of the planes' matrix in Mt w.
  `shape_of_leftAt`: under `K3LeftAt` what the seat finds has the place's shape.
  `reads_at`: every public record that is tied to the hearing (`PubAt`) has true reads of Mt w, in
  the world of every ledger, at the statement's mask row and entries.
  `Plan4L.planes_at`: `K4ReadsTrue` at the ledger behind K4's first run of claims.

Limits. TRUE BY MAKE: the entries are chosen so (EntryTrue.lean's limits): nothing here ties them to
what a prover has committed: that is another row's matter. EVERY LINE OF `ReadsAre` IS A PREMISE:
entry and cell are lines on the letters `Sem`, nu and Mt, which nobody fills here; one and cols are
public numbers, evaluated by nobody here. `planes_at` takes beside: `Meets`, `ValueIs`, the ledger's
sizes, `PubLines`, `LookLines`, the rotary tables' fit, the heard shape. Nothing on soundness. USER:
`Plan4K.owes3_of4` (CloseK4.lean).
-/
import Johnson.Road.K4.CloseRows
import Johnson.Road.K4.LookOfLeft
import Johnson.Road.K4.PlanesAtPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Iop Cb Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Reading Fork Forest.Heard WsShape HTailF2)
open OnBytes.Model.Layer (Own matIx)
open OnBytes.Desc.First.K4 (Par Seat)
open OnBytes.Desc.First.P1 (gl Tg7 aS7)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Behind K04LawAt frontRun)
open VerifiableInference.OnPublicFiles (K4ReadsTrue K3LeftAt)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (LW Dim)

variable {T Wt Cl : Type} {Fr : Frame} {par : Par} {hS : OnBytes.Model.Layer.Shape}
  {pcl : List (List String)}

/-- **Four lines on the reads.** -/
structure ReadsAre (par : Par) (Sm : Sem Wt) (nu : Wt → _root_.Fo.Pl → Cb.Gl.E) (tl : HTailF2)
    (h3 : OnBytes.Model.Forest.Shape) (Mt : Wt → Mats Cb.Gl.E) : Prop where
  /-- the letter for the true value of an entry is filled by the definition -/
  entry : ∀ o w, Sm.entryT o w = entryTrue tl o (Mt w)
  /-- the planes' matrix has its rows in one run -/
  one : (tl.mats.getD (matIx par.P.y).iB {}).m / 2 ^ par.P.y.h.lmb = 1
  /-- it has at least the planes' columns -/
  cols : _root_.Fo.planeCols h3 par.P.y.h.lmb ≤ (tl.mats.getD (matIx par.P.y).iB {}).k
  /-- the planes' cells under nu are its entries -/
  cell : ∀ w, ∀ r < 2 ^ par.P.y.h.lmb, ∀ c < _root_.Fo.planeCols h3 par.P.y.h.lmb,
    Mt w (matIx par.P.y).iB r c = nu w (.cell r c)

/-- Under the sharp promise what the seat finds has the place's shape. -/
theorem shape_of_leftAt (L : Seat T) {h : OnBytes.Model.Forest.Shape} {lm first : ℕ}
    {Q : Fork → Prop} {x : T} (H : K3LeftAt (fun s => some (L.fork s)) L.look h lm first Q x)
    {fo : Forest.Heard} (hl : L.look x = some fo) : fo.shape = h := by
  obtain ⟨F, F', g, rs, _, _, K, hg, _⟩ := H
  obtain rfl : g = fo := Option.some.inj (hg.symm.trans hl)
  exact K.shape

/-- **The reads of Mt w are true at every record that is tied to the hearing.** -/
theorem reads_at (L : Seat T) {pc : Piece (ckP .two) Fr T Cl Wt} {a : T × Fr.E.Str}
    {τ : Tr (uLT (ckP .two) pc.ds)} {fo : Forest.Heard} {o : Own} {G : Fork}
    (Y : Yes L par pc a τ fo o G) {D : Dim} {tb : Tables} {s : WsShape} {lk : ℕ}
    {s0 h3 : OnBytes.Model.Forest.Shape} {tl : HTailF2}
    (B : PubLines { par.P with tokv := L.tokv a.1 } par.g hS pcl D tb s lk s0 tl) (Sm : Sem Wt)
    {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {Mt : Wt → Mats Cb.Gl.E}
    (R : ReadsAre par Sm nu tl h3 Mt) (w : Wt) (Xp : Rows.Pub34 Cb.Gl.E) (G2 : Fork) (t4 : Tape)
    (PX : PubAt Xp { par.P with tokv := L.tokv a.1 } par.hp fo o G2 t4 D tb hS) (Fl : Fork) :
    Xp.ReadsTrue (Fl.worldOf gl (Sm.mask w) (Sm.entryT o w)) (Mt w) := by
  rw [R.entry o w]
  exact reads_of_pubAt PX Y.hears B.hrd B.hmats B.htm B.hNM (Mt w) Fl (Sm.mask w)

variable [scl : Scl] {Mm X : Type} {QL : Plan4L Cb.Gl.E Mm X}

/-- **The three planes' tables' reads are true at the ledger behind the first run.** -/
theorem Plan4L.planes_at (A : QL.plan.Meets par hS pcl) (L : Seat T)
    {pc : Piece (ckP .two) Fr T Cl Wt} {a : T × Fr.E.Str} {τ : Tr (uLT (ckP .two) pc.ds)}
    {fo : Forest.Heard} {o : Own} {G : Fork} (Y : Yes L par pc a τ fo o G)
    (hF : PscRun.Sized (L.fork a.1)) {s : WsShape} {lk : ℕ}
    {s0 h3 : OnBytes.Model.Forest.Shape} {tl : HTailF2}
    (B : PubLines { par.P with tokv := L.tokv a.1 } par.g hS pcl QL.plan.full.D QL.plan.full.tb s
      lk s0 tl)
    (K : LookLines { par.P with tokv := L.tokv a.1 } fo s0)
    (Rp : ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
        QL.plan.full.D QL.plan.full.tb (par.g * par.P.y.Lam) lam)
    (V : Plan4L.ValueIs QL par hS) (Sm : Sem Wt) {nu : Wt → _root_.Fo.Pl → Cb.Gl.E}
    {Mt : Wt → Mats Cb.Gl.E} (R : ReadsAre par Sm nu tl h3 Mt) (hsh : fo.shape = h3) (w : Wt)
    {fs₁ : Array OnBytes.Model.Aff} {F₁ : Fork} (h1 : frontRun par o G = some (fs₁, F₁)) :
    K4ReadsTrue gl o.v fo F₁ (nu w) (Sm.entryT o w) := by
  obtain ⟨hinv, _, hvy, _, _, _⟩ :=
    Plan4L.heard_K A Y.hears hF (small_of_all _ _ _ Y.small) V.scl V.L0
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, Ld⟩ := own_led7 hF Y.hears A.hg
  obtain ⟨Xp, PX, _, _⟩ := pubAtMore_of_led Y.hears Ld B K Rp hinv
  have e := k4ReadsTrue_of_front PX Y.hears B.hrd B.hmats B.htm B.hNM (Mt w) F₁ (nu w)
    (by rw [hvy]; exact R.one) (by rw [hvy, PX.fo, hsh]; exact R.cols)
    (by rw [hvy, PX.fo, hsh]; exact R.cell w) h1
  rw [PX.fo, ← R.entry o w] at e
  exact e

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.shape_of_leftAt
#print axioms OnBytes.Road.K4.reads_at
#print axioms OnBytes.Road.K4.Plan4L.planes_at
