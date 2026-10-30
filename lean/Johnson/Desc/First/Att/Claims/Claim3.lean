-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Claim3.lean: kind K5, the claims are the written lists: the first
readers and the plane values of claim 3. The routines of Johnson/Desc/First/Att/RunsP.lean, on the
kind's own records, are held against the written forms and lists of OnBytes/Tie/Pv/Lookup/Ends/, at
the kind's records made of a plain record h : Attention.Heard (`inOld`).

Main names:
  `tabsOld`, `inOld`: the records of OnBytes/Model as the kind's.
  `gv_u3at`, `gv_weighted`, `gv_lessPieces`, `gv_plane`, `gv_linPlanes`: wherever the kind's routine
    returns at K it returns the written form and has gathered the written list.
Used of OnBytes: plain records, pure functions and definitions alone; no routine in a context and no
theorem on a run: the record Attention.Heard and its parts; the written forms and lists Fo.u3Form,
weightedF, lessF, planeF, linPlanesT, callKRV, callKRT, claim3V, claim3T.
Not claimed: that a routine returns; what a form is worth.

Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAttListsTop
import Johnson.Desc.First.Att.SeatC
import Johnson.Desc.First.Att.Claims.GV

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (TablesP ScoreT Fun1 geoOf ptsOfOwn w1Of)

variable {K : ℕ}

/-- The kind's record of tables made of that of OnBytes/Model, field by field. The list for the smallness test is left empty: no run reads it. -/
def tabsOld (t : Attention.Tables) : TablesP :=
  { ptM := t.ptM, ptD := t.ptD, tA := t.tA, tVM := t.tVM, tVD := t.tVD
    score := t.score.map fun s => { tM := s.tM, tQ := s.tQ, tK := s.tK }
    hW := t.hW, hX := t.hX, hE := t.hE, hT := t.hT, hPi := t.hPi, hR2 := t.hR2, tO := t.tO
    qO := t.qO, qVM := t.qVM, qVD := t.qVD, qF := t.qF, qKx := t.qKx
    tBit0 := t.tBit0, tBit1 := t.tBit1, tPin := t.tPin, tabLen := t.tabLen, funs := #[] }

/-- What the kind's runs read, made of a plain record of OnBytes/Model. -/
def inOld (h : Attention.Heard) : P.Runs.In :=
  { g := geoOf h.S, p := ptsOfOwn h.planes h.scores h.d h.x, t := tabsOld h.t, zk := h.g.zk, iU3 := h.iU3 }

theorem gv_mustAs (name : String) (b : Bool) : GV K (P.Runs.mustAs name b) () [] := by
  unfold P.Runs.mustAs
  split
  · exact GV.pure ()
  · exact GV.failure _ _

theorem gv_refuse {α : Type} (name : String) (v : α) (l : List Aff) : GV K (P.Runs.refuse name : P.Runs.W α) v l :=
  GV.failure _ _

theorem gv_uEnt (t x : ℕ) : GV K (P.Runs.uEnt t x) (Fo.u3Form t K x) [] := by
  unfold P.Runs.uEnt
  exact GV.bind0 GV.read (GV.bind0 (gv_mustAs _ _) (GV.pure _))

theorem gv_u3at (h : P.Runs.In) (t i : ℕ) : GV K (P.Runs.u3at h t i) (Fo.u3Form h.iU3 K (t + i)) [] := by
  unfold P.Runs.u3at
  exact GV.bind0 (gv_mustAs _ _) (gv_uEnt h.iU3 (t + i))

theorem gv_weighted (n : ℕ) (w : Array E) (f : ℕ → P.Runs.W Aff) (fv : ℕ → Aff)
    (hf : ∀ i, GV K (f i) (fv i) []) : GV K (P.Runs.weighted n w f) (Fo.weightedF n w fv) [] := by
  unfold P.Runs.weighted Fo.weightedF
  exact GV.foldlM0 _ (fun s i => Aff.addMul s (fv i) (w.getD i zeroE))
    (fun s i => GV.bind0 (hf i) (GV.pure _)) _ _

/-- The pieces of the kind's record are those of the record of OnBytes/Model, three fields each. -/
theorem gv_lessPieces (start : Aff) (pw : Array PW) (f : P.W1 → P.Runs.W Aff) (fv : PW → Aff)
    (hf : ∀ w : PW, GV K (f { lam := w.lam, a := w.a, wp := w.wp }) (fv w) []) :
    GV K (P.Runs.lessPieces start (w1Of pw) f) (Fo.lessF start pw fv) [] := by
  unfold P.Runs.lessPieces Fo.lessF w1Of
  rw [← Array.foldlM_toList, Array.toList_map, List.foldlM_map]
  exact GV.foldlM0 _ (fun s w => Aff.addMul s (fv w) (mulE minusOne w.wp))
    (fun s w => GV.bind0 (hf w) (GV.pure _)) _ _

theorem gv_plane (h : Attention.Heard) (t x lam a : ℕ) (z : Array E) (isD : Bool) :
    GV K (P.Runs.plane (inOld h) t x lam a z isD) (Fo.planeF h K t x lam a z isD) [] := by
  unfold P.Runs.plane Fo.planeF
  exact gv_weighted _ _ _ _ fun _ => gv_u3at (inOld h) t _

/-- linPlanes at a plane claim of the record of OnBytes/Model. -/
theorem gv_linPlanes (h : Attention.Heard) (pc : PlaneClaim) :
    GV K (P.Runs.linPlanes (inOld h) { call := pc.call, z := pc.z, isD := pc.isD, pw := w1Of pc.pw, s0 := pc.s0, np := pc.np })
      () (Fo.linPlanesT h K pc) := by
  unfold P.Runs.linPlanes Fo.linPlanesT
  exact GV.forM _ _ (fun x => GV.bind0 (gv_lessPieces _ _ _ _ fun w => gv_plane h _ _ _ _ _ _) (GV.lin _)) _

end K5Law
