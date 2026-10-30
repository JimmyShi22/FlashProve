-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseReadsFirst.lean: AT A YES OF THE PIECE THAT HOLDS K4's BLOCK, IN THE FIRST
GROUP: THE THREE PLANES' TABLES' TRUE READS, WHERE THE STATEMENT's LETTER FOR THE TRUE VALUE OF AN
ENTRY IS FILLED BY THE DEFINITION `entryTrue` (Johnson/Road/K4/EntryTrue.lean). The twin of
`Plan4L.planes_at` (Johnson/Road/K4/CloseReads.lean). One theorem. Glue: `k4ReadsTrue_of_front`
(PlanesAtPub.lean) laid at a `Yes`, over `Plan4LF.heard_KF` and `pubAtMore_of_ledF`
(CloseKitFirst.lean). No draw, no count. CloseReads.lean's record `ReadsAre` and its theorems
`shape_of_leftAt` and `reads_at` name no group and serve the first group as they stand.

  `Plan4LF.planes_atF`: `K4ReadsTrue` at the ledger behind K4's first run of claims.

Limits. K04_law IS NOT PROVED BY THIS. TRUE BY MAKE: the entries are chosen so (EntryTrue.lean's
limits): nothing here ties them to what a prover has committed. EVERY LINE OF `ReadsAre` IS A
PREMISE. `planes_atF` takes beside: `MeetsF`, `ValueIs` at the letters that the value shares with a
later group's, the ledger's sizes, `PubLines`, `LookLines`, the rotary tables' fit, the heard shape.
Nothing on soundness. USER: `Plan4KF.owes3F_of4` (CloseK4First.lean).
-/
import Johnson.Road.K4.CloseReads
import Johnson.Road.K4.CloseKitFirst

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
open OnBytes.Desc.First.P1 (gl)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem frontRun)
open VerifiableInference.OnPublicFiles (K4ReadsTrue)
open Inst.Model (Scl)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)} {QF : Plan4LF Cb.Gl.E Mm X}

/-- **The three planes' tables' reads are true at the ledger behind the first run, in the first
group**, under `MeetsF`, the ledger's sizes, `PubLines`, `LookLines`, the rotary tables' fit,
`ValueIs`, `ReadsAre` and the heard shape. -/
theorem Plan4LF.planes_atF (A : QF.planF.MeetsF par hS pcl) (L : Seat T)
    {pc : Piece (ckP .two) Fr T Cl Wt} {a : T × Fr.E.Str} {τ : Tr (uLT (ckP .two) pc.ds)}
    {fo : Forest.Heard} {o : Own} {G : Fork} (Y : Yes L par pc a τ fo o G)
    (hF : PscRun.Sized (L.fork a.1)) {s : WsShape} {lk : ℕ}
    {s0 h3 : OnBytes.Model.Forest.Shape} {tl : HTailF2}
    (B : PubLines { par.P with tokv := L.tokv a.1 } par.g hS pcl QF.planF.fullF.D
      QF.planF.fullF.tb s lk s0 tl)
    (K : LookLines { par.P with tokv := L.tokv a.1 } fo s0)
    (Rp : ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
        QF.planF.fullF.D QF.planF.fullF.tb (par.g * par.P.y.Lam) lam)
    (V : Plan4L.ValueIs QF.toPlan4L par hS) (Sm : Sem Wt) {nu : Wt → _root_.Fo.Pl → Cb.Gl.E}
    {Mt : Wt → Mats Cb.Gl.E} (R : ReadsAre par Sm nu tl h3 Mt) (hsh : fo.shape = h3) (w : Wt)
    {fs₁ : Array OnBytes.Model.Aff} {F₁ : Fork} (h1 : frontRun par o G = some (fs₁, F₁)) :
    K4ReadsTrue gl o.v fo F₁ (nu w) (Sm.entryT o w) := by
  obtain ⟨hinv, _, hvy, _, _, _⟩ :=
    Plan4LF.heard_KF A Y.hears hF (small_of_all _ _ _ Y.small) V.scl V.L0
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, Ld⟩ := own_ledG hF Y.hears
  obtain ⟨Xp, PX, _, _⟩ := pubAtMore_of_ledF Y.hears Ld B K Rp hinv
  have e := k4ReadsTrue_of_front PX Y.hears B.hrd B.hmats B.htm B.hNM (Mt w) F₁ (nu w)
    (by rw [hvy]; exact R.one) (by rw [hvy, PX.fo, hsh]; exact R.cols)
    (by rw [hvy, PX.fo, hsh]; exact R.cell w) h1
  rw [PX.fo, ← R.entry o w] at e
  exact e

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4LF.planes_atF
