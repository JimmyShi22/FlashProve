-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/ReadsTokens.lean: the layers' instance of the planes' law at the record WITH the
request's tokens, the plans being those of the record that holds none.

The text that runs hears at the public record of the layers with the request's tokens laid in
({ P0 with tokv := z }), and the hearing reads them. The public list of plans is what Layer.plansG
returns at the record P0, which holds no token yet. In Johnson/Meaning/ReadsPublic.lean's
`k4_host_planes_public` one letter stands for both. Layer.planG reads no token; so the two part
here.

Main theorems (namespace `Meaning.Reads`).
  `planG_tokens`: planG at { P0 with tokv := z } is planG at P0.
  `k4_host_planes_tokens`: **the three clauses at the layers' forms**: the run, the tails and the
      letters at { P0 with tokv := z }; the list of plans at P0.
  `k4_member_plan`: the premises of `k4_host_planes_plan` on the letters, the world and the planes'
      cells can be met together at the letters' very type: the plan's record, closed with the public
      shapes; whatever small integers stand in the cells.
  `k4_plan_not_empty`: so from a run, planesParts, the tails, the group's number and the plan alone:
      there are letters, a world and a reading of the lookup's places at which the three clauses
      hold.

Limits. As Johnson/Meaning/ReadsPlan.lean's. The members are made: no file, no run, nothing
committed. That the layers' block is seated at the public record's own members is not shown. Nothing
on soundness.
-/
import Johnson.Meaning.ReadsPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Reads
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop
open OnBytes.Model.Layer (Pub Own HPlan2 matIx tailsOf planG plansG)
open OnBytes.K.Kc
open Meaning.Planes

/-- The plan of a group reads no token. -/
theorem planG_tokens (P0 : Pub) (z : Array ℕ) (g : ℕ) (O : Option HPlan2) :
    planG { P0 with tokv := z } g O = planG P0 g O := rfl

/-- **The three clauses at the layers' forms, at the record with the tokens**, hp being a member of
the list of plans of the record that holds none. -/
theorem k4_host_planes_tokens (ρ : Reading Cb.Gl.E) {P0 : Pub} {z : Array ℕ} {hp : HPlan2}
    {g : ℕ} {fo : Forest.Heard} {F F' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl { P0 with tokv := z } hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P0.tails = tailsOf P0.y) {G : Array HPlan2} (hG : plansG P0 = .ok G)
    (hgp : G[g]? = some hp)
    (zb0 zb1 : List Cb.Gl.E) (hz0 : rdL ρ o.H.fo.zb0 = zb0) (hz1 : rdL ρ o.H.fo.zb1 = zb1)
    (Θ : TLetters Cb.Gl.E (Tie.Pv.Tail.sizeOf
      (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g))))
    {x : Θ.X} {msg : Θ.M} (h : relIn Θ.letters x msg)
    (hphi : ∀ n Fn, o.funs.toList[n]? = some Fn → ∀ j, j < Fn.len →
      Θ.phi x n j = ρ.val (Fn.phi.getD j zeroE))
    (W : World Cb.Gl.E)
    (hu : ∀ f ∈ o.funs.toList, f.tree = 2 → ∀ c < (hp.tl.mats.getD f.mat {}).k,
      ∀ sg < (hp.tl.mats.getD f.mat {}).m / f.len,
        Θ.u3 msg (f.start + c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg) =
          u3Val W.entry o.v.iU3 o.v.K3
            (f.start + c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg))
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellN (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g)) Θ msg
        (matIx o.v.y).iB r c = ν (.cell r c)) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb zb0 zb1 ν (fun f => f.value ρ W)
        (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨⟨O, hO⟩, hg⟩ := plan_of_plansG hG hgp
  exact k4_host_planes_plan ρ hh hq hT hg ((planG_tokens P0 z g O).trans hO) zb0 zb1 hz0 hz1 Θ h
    hphi W hu ν h4

/-- **The premises on the letters, the world and the planes' cells hold together at the letters'
very type**, whatever small integers stand in the matrices' cells. -/
theorem k4_member_plan (ρ : Reading Cb.Gl.E) {P : Pub} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {F F' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t')) {O : Option HPlan2}
    (hplan : planG P g O = .ok hp) (a : ℕ → ℕ → ℕ → ℤ)
    (small : ∀ μ c i, |a μ c i| < 2 * ((2 ^ lbz : ℕ) : ℤ)) :
    ∃ (Θ : TLetters Cb.Gl.E (Tie.Pv.Tail.sizeOf (Closed.closedAt hp.tl (Closed.layShapes P g))))
      (x : Θ.X) (msg : Θ.M) (W : World Cb.Gl.E) (ν : _root_.Fo.Pl → Cb.Gl.E),
      relIn Θ.letters x msg ∧
      (∀ n Fn, o.funs.toList[n]? = some Fn → ∀ j, j < Fn.len →
        Θ.phi x n j = ρ.val (Fn.phi.getD j zeroE)) ∧
      (∀ pos, Θ.u3 msg pos = u3Val W.entry o.v.iU3 o.v.K3 pos) ∧
      ∀ r c, cellN (Closed.closedAt hp.tl (Closed.layShapes P g)) Θ msg (matIx o.v.y).iB r c =
        ν (.cell r c) := by
  obtain ⟨Θ, x, msg, W, h1, h2, h3, _⟩ := k4_member ρ hh
    (Closed.closedAt hp.tl (Closed.layShapes P g)) (k4_hsh hh hp.tl)
    (sizes_of_map (Road.planG_sizes hplan).1) a small
  refine ⟨Θ, x, msg, W, fun p => match p with
    | .cell r c => cellN (Closed.closedAt hp.tl (Closed.layShapes P g)) Θ msg (matIx o.v.y).iB r c
    | _ => 0, h1, h2, h3, fun _ _ => rfl⟩

/-- **From a run, planesParts, the tails, the group's number and the plan alone**: there are
letters, a world and a reading of the lookup's places at which the three clauses hold. -/
theorem k4_plan_not_empty (ρ : Reading Cb.Gl.E) {P : Pub} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {F F' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P.tails = tailsOf P.y) (hg : g < P.y.NGr) {O : Option HPlan2}
    (hplan : planG P g O = .ok hp) :
    ∃ (W : World Cb.Gl.E) (ν : _root_.Fo.Pl → Cb.Gl.E) (tB0 tB1 tP : ℕ),
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL ρ o.H.fo.zb0) (rdL ρ o.H.fo.zb1) ν
        (fun f => f.value ρ W) (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨Θ, x, msg, W, ν, h1, h2, h3, h4⟩ := k4_member_plan ρ hh hplan (fun _ _ _ => 0)
    (fun _ _ _ => by norm_num [lbz])
  obtain ⟨tB0, tB1, tP, _, _, _, H⟩ := k4_host_planes_plan ρ hh hq hT hg hplan _ _ rfl rfl Θ h1 h2
    W (fun _ _ _ _ _ _ _ => h3 _) ν (fun r _ c _ => h4 r c)
  exact ⟨W, ν, tB0, tB1, tP, H⟩

#print axioms planG_tokens
#print axioms k4_host_planes_tokens
#print axioms k4_member_plan
#print axioms k4_plan_not_empty

end Meaning.Reads
