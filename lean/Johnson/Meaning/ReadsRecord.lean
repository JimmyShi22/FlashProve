-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/ReadsRecord.lean: one public record of the smallness test serves the layers' row:
the premise on the tables' shapes of Johnson/Meaning/ReadsK4.lean's `k4_host_planes_cells`, paid at
the library's closed record.

`k4_host_planes_cells` takes a record tl for its sizes alone and asks (hsh) that its tables have the
matrices, lengths and first entries of the tables that the layers' hearing has left. The library has
the shapes as a term of the public record (`layShapes P g`, OnBytes/Tie/Pv/Tail/ShapesLay.lean) and
a closed record with given shapes and no weight (`closedAt tl sh`,
OnBytes/Tie/Pv/Tail/ClosedRec.lean).

Main theorems (namespace `Meaning.Reads`).
  `hear_layShapes`: the tables that a run of the layers' plain hearing leaves have the shapes
      `layShapes P g`.
  `closed_tabs`: the closed record's tables have the shapes that it was given.
  `k4_hsh`: so hsh holds at `closedAt tl (layShapes P g)`, for every record tl.
  `k4_host_planes_closed`: `k4_host_planes_cells` at that record, without hsh.

Limits. The other premises of `k4_host_planes_cells` stay; of those on the record: its matrices have
the sizes of the group's list, and each table's matrix is one of them. That the smallness test is
seated at this record is not shown. Nothing on soundness.
-/
import Johnson.Meaning.ReadsK4
import OnBytes.Tie.Pv.Tail.ShapesLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Reads
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop
open OnBytes.Model.Layer (Pub Own HPlan2 matIx tailsOf)
open OnBytes.K.Kc
open Meaning.Planes

/-- The hearing's tables have the public record's term of shapes. -/
theorem hear_layShapes {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t')) :
    o.funs.toList.map (fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) = Closed.layShapes P g := by
  obtain ⟨laid, hl, e⟩ := hear_shapes hh
  unfold Closed.layShapes
  rw [hl, e]
  show shapesOf laid = Closed.laidShapes laid
  unfold shapesOf Closed.laidShapes
  rw [List.flatMap_def]

/-- The closed record's tables have the shapes that it was given. -/
theorem closed_tabs (tl : HTailF2) (sh : List Tab) :
    (Tie.Pv.Tail.sizeOf (Closed.closedAt tl sh)).tabs = sh := by
  show ((Closed.funsOf sh fun _ => #[]).toList.map
    fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) = sh
  unfold Closed.funsOf
  rw [List.toList_toArray]
  exact Closed.funsL_shapes sh _

/-- **The premise on the shapes, at the closed public record.** -/
theorem k4_hsh {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    (tl : HTailF2) :
    (Tie.Pv.Tail.sizeOf (Closed.closedAt tl (Closed.layShapes P g))).tabs =
      o.funs.toList.map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab) := by
  rw [closed_tabs, hear_layShapes hh]

/-- **The three clauses at the layers' forms, at the closed public record**: `k4_host_planes_cells`
without its premise on the shapes. tl0: any record; of it the closed record keeps the matrices and
their number. -/
theorem k4_host_planes_closed (ρ : Reading Cb.Gl.E) {P : Pub} {hp : HPlan2}
    {g : ℕ} {fo : Forest.Heard} {F F' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P.tails = tailsOf P.y) (hg : g < P.y.NGr)
    (zb0 zb1 : List Cb.Gl.E) (hz0 : rdL ρ o.H.fo.zb0 = zb0) (hz1 : rdL ρ o.H.fo.zb1 = zb1)
    (tl0 : HTailF2)
    (Θ : TLetters Cb.Gl.E (Tie.Pv.Tail.sizeOf (Closed.closedAt tl0 (Closed.layShapes P g))))
    {x : Θ.X} {msg : Θ.M} (h : relIn Θ.letters x msg)
    (hmat : ∀ μ, (tl0.mats.getD μ {}).m = ((P.tails.getD g {}).mats.getD μ {}).m ∧
      (tl0.mats.getD μ {}).k = ((P.tails.getD g {}).mats.getD μ {}).k)
    (hNM : ∀ f ∈ o.funs.toList, f.tree = 2 → f.mat < tl0.NM)
    (hphi : ∀ n Fn, o.funs.toList[n]? = some Fn → ∀ j, j < Fn.len →
      Θ.phi x n j = ρ.val (Fn.phi.getD j zeroE))
    (W : World Cb.Gl.E)
    (hu : ∀ f ∈ o.funs.toList, f.tree = 2 → ∀ c < (tl0.mats.getD f.mat {}).k,
      ∀ sg < (tl0.mats.getD f.mat {}).m / f.len,
        Θ.u3 msg (f.start + c * ((tl0.mats.getD f.mat {}).m / f.len) + sg) =
          u3Val W.entry o.v.iU3 o.v.K3 (f.start + c * ((tl0.mats.getD f.mat {}).m / f.len) + sg))
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellN (Closed.closedAt tl0 (Closed.layShapes P g)) Θ msg (matIx o.v.y).iB r c =
        ν (.cell r c)) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb zb0 zb1 ν (fun f => f.value ρ W)
        (k4Bit o.v tB0 tB1) (k4Pin o.v tP) :=
  k4_host_planes_cells ρ hh hq hT hg zb0 zb1 hz0 hz1
    (Closed.closedAt tl0 (Closed.layShapes P g)) Θ h (k4_hsh hh tl0) hmat hNM hphi W hu ν h4

#print axioms k4_host_planes_closed
#print axioms hear_layShapes
#print axioms closed_tabs
#print axioms k4_hsh

end Meaning.Reads
