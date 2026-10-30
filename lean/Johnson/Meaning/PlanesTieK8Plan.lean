-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PlanesTieK8Plan.lean: two premises on the plan's record fall from the rows of
Johnson/Meaning/PlanesTieK8.lean.

Johnson/Goal/Meaning/PlanPort.lean shows of every record that `Layer.planG` returns: it names one
symbol array for each matrix (`planG_gt`), and the array of the reads has as many columns as the
plan's number of reads (`planG_K3`). With what a run of the layers' hearing says of its own numbers
(`hear_iU3`, Johnson/Meaning/ReadsK4.lean) these pay hK and hgt.

Main theorems (namespace `Meaning.Reads`).
  `k4_K3`: behind a run of the hearing at a plan that planG returns, K3 IS the plan's number of
      reads.
  `k4_hK`: so hK: the plan's number of reads is at most K3; at a member of the public list of plans.
  `k4_hgt`: hgt: the plan's record, closed with any shapes, names a symbol array for each matrix.
  `k4_hu_portWorld_plan`: `k4_hu_portWorld` without hK.
  `k4_host_planes_of_relA_plan`: `k4_host_planes_of_relA` without hK and hgt.

OBJECT · USER · LETTERS. Object: the library's `Layer.planG` | `plansG`, the layers' plain hearing
`Desc.First.K4.hearFl`, and in the last theorem `layReads ... .relA`
(Johnson/Desc/First/K8/LawLay.lean). No seated description is named. User: the planes' row at the
seated description. Letters: LawLay.lean's, as in Johnson/Meaning/PlanesTieK8.lean.



Compiled with the whole library.

Limits. As Johnson/Meaning/PlanesTieK8.lean's; all its other premises stand. Nothing on soundness.

-/
import Johnson.Meaning.PlanesTieK8
import Johnson.Goal.Meaning.PlanPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Reads
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop
open OnBytes.Model.Layer (Pub Own HPlan2 matIx tailsOf planG plansG)
open OnBytes.K.Kc
open Meaning.Planes

/-- **Behind a run of the hearing at a plan that planG returns, K3 is the plan's number of reads.**
-/
theorem k4_K3 {P P' : Pub} {hp : HPlan2} {g g' : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    {O : Option HPlan2} (hO : planG P' g' O = .ok hp) : o.v.K3 = hp.nU.getD 2 0 := by
  rw [(hear_iU3 hh).2]
  exact Meaning.Plan.planG_K3 P' g' O hp hO (hear_iU3 hh).1

/-- hK, at a member of the public list of plans. -/
theorem k4_hK {P P0 : Pub} {hp : HPlan2} {g g' : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    {Gp : Array HPlan2} (hG : plansG P0 = .ok Gp) (hgp : Gp[g']? = some hp) :
    hp.nU.getD 2 0 ≤ o.v.K3 := by
  obtain ⟨⟨O, hO⟩, _⟩ := plan_of_plansG hG hgp
  exact Nat.le_of_eq (k4_K3 hh hO).symm

/-- hgt, at a member of the public list of plans. -/
theorem k4_hgt {P0 : Pub} {hp : HPlan2} {g : ℕ} {Gp : Array HPlan2} (hG : plansG P0 = .ok Gp)
    (hgp : Gp[g]? = some hp) (sh : List Tab) :
    (Closed.closedAt hp.tl sh).NM ≤ (Closed.closedAt hp.tl sh).gtTree.size := by
  obtain ⟨⟨O, hO⟩, _⟩ := plan_of_plansG hG hgp
  show hp.tl.NM ≤ hp.tl.gtTree.size
  exact Nat.le_of_eq (Meaning.Plan.planG_gt _ _ O hp hO).symm

/-- `k4_hu_portWorld` without hK. -/
theorem k4_hu_portWorld_plan {P0 : Pub} {z : Array ℕ} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard}
    {Fk Fk' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl { P0 with tokv := z } hp g fo Fk t = some (o, Fk', t'))
    {Gp : Array HPlan2} (hG : plansG P0 = .ok Gp) (hgp : Gp[g]? = some hp)
    {J : Type} [Fintype J] (Y : Lay J) (Fs : Fork)
    (m : J → Cb.Gl.E) (hr : RowsBelow Y Fs o.v.iU3) (h1 : UnitRow Fs o.v.iU3) :
    ∀ f ∈ o.funs.toList, f.tree = 2 → ∀ c < (hp.tl.mats.getD f.mat {}).k,
      ∀ sg < (hp.tl.mats.getD f.mat {}).m / f.len,
        Y.cellAt m o.v.iU3 0 (f.start + c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg) =
          u3Val (portWorld Reading.gl Y Fs m).entry o.v.iU3 o.v.K3
            (f.start + c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg) :=
  k4_hu_portWorld hh hG hgp (k4_hK hh hG hgp) Y Fs m hr h1

section AtTheLetters
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.Sound OnBytes.Maker Johnson.Pack

variable {J : Type} [Fintype J] (Y : Lay J) (tl0 : HTailF2) (cs : OnBytes.Codes)
  (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  {Cells Tok : Type} (entE : (sigOf cs l).Msg → J → Cb.Gl.E)
  (entW : Wit Cells Tok MsgT → J → Cb.Gl.E)
  {Xi : Type} (G : FileDescription Xi) (smpOf : S → (sigOf cs l).Smp)
  (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
    smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)
  (Cl : Type) (F : Frame) (p : K8.Par) (base e : ℕ) (hseat : ∀ i, (seat' i).1 < base)

/-- `k4_host_planes_of_relA` without hK and hgt. -/
theorem k4_host_planes_of_relA_plan {P0 : Pub} {z : Array ℕ} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {Fk Fk' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl { P0 with tokv := z } hp g fo Fk t = some (o, Fk', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P0.tails = tailsOf P0.y) {Gp : Array HPlan2} (hG : plansG P0 = .ok Gp)
    (hgp : Gp[g]? = some hp)
    (e0 : tl0 = Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g))
    (hE : ∀ w j, early tl0 (Y.addr j) = true → entE (msgsOf cs l seat' arr w) j = entW w j)
    (a : S × F.E.Str) (w : Wit Cells Tok MsgT) (tl : HTailF2) (ht : a.1.tl? = some tl)
    (hp0 : SameLay (K8.recOf tl0 a.1) tl0) (hz : SameSize tl tl0)
    (h : (layReads Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).relA a w)
    (hfun : tl.funs = o.funs) :
    ∃ b : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
        |b μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
          Y.cellAt (entW w) (tl.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => b μ i c) i' : ℤ) :
              Cb.Gl.E)) ∧
      ∀ (ν : _root_.Fo.Pl → Cb.Gl.E) (W : World Cb.Gl.E),
        (∀ pos < o.v.K3, W.entry o.v.iU3 0 pos = Y.cellAt (entW w) o.v.iU3 0 pos) →
        (∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
          ((b (matIx o.v.y).iB r c : ℤ) : Cb.Gl.E) = ν (.cell r c)) →
        ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
          o.v.tabAt "b-pin" = some tP ∧
          K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL Reading.gl o.H.fo.zb0)
            (rdL Reading.gl o.H.fo.zb1) ν (fun f => f.value Reading.gl W)
            (k4Bit o.v tB0 tB1) (k4Pin o.v tP) :=
  k4_host_planes_of_relA Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat hh hq hT hG
    hgp e0 hE (by rw [e0]; exact k4_hgt hG hgp _) a w tl ht hp0 hz h hfun (k4_hK hh hG hgp)

end AtTheLetters

#print axioms k4_K3
#print axioms k4_hK
#print axioms k4_hgt
#print axioms k4_hu_portWorld_plan
#print axioms k4_host_planes_of_relA_plan

end Meaning.Reads
